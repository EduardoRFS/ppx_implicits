open Ocaml_typing;
open Parsetree;
open Typedtree;

// declaration

let (let.some) = Option.bind;
// code -> hacked typechecker and transform to classic -> untype -> (ocaml typechecker -> compile)

module Env_stack = {
  let last_modtype = ref(0);
  type data = {
    binding_loc: Location.t,
    source_env: Env.t,
    scope: int,
    // TODO: they need to be ordered
    mutable modtypes:
      list((Typedtree.module_type_declaration, Types.modtype_declaration)),
  };
  type t = Stack.t(data);

  let stack = Stack.create();

  let push = (~scope, binding_loc, source_env) =>
    Stack.push({scope, binding_loc, source_env, modtypes: []}, stack);
  let append_modtype = (~loc, signature, env) => {
    let data = Stack.top(stack);
    let name = Printf.sprintf("HKT_Magic_%d", last_modtype^);
    incr(last_modtype);
    // copied from transl_modtype_decl_aux
    let tmty =
      Typetexp.transl_modtype^(
        data.source_env,
        {
          pmty_desc: Pmty_signature(signature),
          pmty_attributes: [],
          pmty_loc: loc,
        },
      );
    let modtype_decl = {
      Types.mtd_type: Some(tmty.mty_type),
      mtd_attributes: [],
      mtd_loc: loc,
      mtd_uid: Types.Uid.mk(~current_unit=Env.get_unit_name()),
    };
    let (id, env) =
      Env.enter_modtype(~scope=data.scope, name, modtype_decl, env);
    let tree_modtype_decl = {
      mtd_id: id,
      mtd_name: {
        txt: name,
        loc,
      },
      mtd_type: Some(tmty),
      mtd_attributes: [],
      mtd_loc: loc,
    };
    data.modtypes = [(tree_modtype_decl, modtype_decl), ...data.modtypes];
    (env, name);
  };
  let pop = (desc, desc_signature, env) => {
    let data = Stack.pop(stack);
    if (data.modtypes == []) {
      (desc, desc_signature, env);
    } else {
      let modtypes = List.rev(data.modtypes);
      let env =
        List.fold_left(
          (env, ({mtd_id, _}, modtype)) =>
            // TODO: what happens if double add
            Env.add_modtype(mtd_id, modtype, env),
          env,
          modtypes,
        );
      // TODO: is it okay to use the final env for all of them?
      let modtypes_declarations =
        List.map(
          ((modtype, _)) =>
            {
              str_desc: Tstr_modtype(modtype),
              str_loc: modtype.mtd_loc,
              str_env: env,
            },
          modtypes,
        );
      let structure =
        modtypes_declarations
        @ [{str_desc: desc, str_loc: data.binding_loc, str_env: env}];
      let signature =
        List.map(
          (({mtd_id, _}, modtype)) =>
            Types.Sig_modtype(mtd_id, modtype, Exported),
          modtypes,
        )
        @ desc_signature;
      let modexpr = {
        mod_desc:
          Tmod_structure({
            str_items: structure,
            str_type: signature,
            str_final_env: env,
          }),
        mod_loc: data.binding_loc,
        mod_type: Mty_signature(signature),
        mod_env: env,
        mod_attributes: [],
      };
      let scope = Ctype.create_scope();

      // this will rescope everything in the signature
      let (signature, env) = Env.enter_signature(~scope, signature, env);

      let return_include = {
        incl_mod: modexpr,
        incl_type: signature,
        incl_loc: data.binding_loc,
        incl_attributes: [],
      };
      (Tstr_include(return_include), signature, env);
    };
  };
};

let with_module = (env, mod_name, modtype, body) => {
  let ident = Ident.create_persistent(mod_name);
  let env = Env.add_module(ident, Mp_present, modtype, env);
  Typecore.type_expression(env, body);
};

// used to avoid instantiating original type
let clone_type_expr = expr => {
  let desc =
    Btype.copy_type_desc(
      ~keep_names=true,
      expr => {
        let clone = Btype.newty2(expr.level, expr.desc);
        clone.scope = expr.scope;
        clone;
      },
      expr.Types.desc,
    );
  let clone = Btype.newty2(expr.Types.level, desc);
  clone.scope = expr.scope;
  clone;
};
let hack_pexp_fun =
    (
      f,
      env: Env.t,
      ty_expect_explained,
      exp_loc,
      l,
      spat: Parsetree.pattern,
      sbody,
    ) => {
  // TODO: do I need to actually run copy_type_desc?
  // TODO: also Ctype.save_levels
  let snapshot = Btype.snapshot();
  let snapshot_levels = Ctype.save_levels();

  try({
    let ty_expect_explained_clone =
      Typecore.mk_expected(
        ~explanation=?ty_expect_explained.Typecore.explanation,
        clone_type_expr(ty_expect_explained.Typecore.ty),
      );
    let expr = f(env, ty_expect_explained_clone, exp_loc, l, spat, sbody);
    Ctype.unify(env, ty_expect_explained.ty, ty_expect_explained_clone.ty);
    expr;
  }) {
  | Typecore.Error(_loc, _env, Expr_type_clash([_, Escape(_)], _, _)) as exn =>
    switch (spat.ppat_desc) {
    | Ppat_constraint(
        {
          ppat_desc: Ppat_unpack({txt: Some(mod_id_name), loc: mod_id_loc}),
          _,
        },
        {ptyp_desc: Ptyp_package((modtype_id, [])), ptyp_loc: typ_loc, _},
      ) =>
      Btype.backtrack(snapshot);
      Ctype.set_levels(snapshot_levels);
      let b = {
        let (_, modtype_decl) =
          Env.lookup_modtype(~loc=modtype_id.loc, modtype_id.txt, env);
        let.some modtype = modtype_decl.mtd_type; // TODO: Option.get bad
        switch (with_module(env, mod_id_name, modtype, sbody)) {
        | {exp_type: typ, exp_loc: loc, _} =>
          // Format.printf("%a\n%!", Printtyp.type_expr, typ);
          let mod_name = Location.{txt: mod_id_name, loc: mod_id_loc};
          let (free_variables, signature) =
            Codegen_wrapper_modtype.make_wrapper_signature({
              pattern_loc: spat.ppat_loc,
              param_name: mod_name,
              param_modtype: modtype_id,
              body_type: {
                txt: typ,
                loc,
              },
            });
          let (env, modtype_name) =
            Env_stack.append_modtype(~loc=typ_loc, signature, env);
          let fn =
            Codegen_function_declaration.transform_function(
              {
                exp_loc,
                pattern_loc: spat.ppat_loc,
                body_loc: sbody.pexp_loc,
                free_variables,
                mod_name,
                modtype_name: {
                  txt: modtype_name,
                  loc: typ_loc,
                },
              },
              sbody,
            );
          // Format.printf("%a\n%!", Pprintast.expression, fn);
          // TODO: is okay to store and restore like this?
          // TODO: copy in_function here
          Some(Typecore.type_expect(env, fn, ty_expect_explained));
        | exception _ => None
        };
      };
      switch (b) {
      | Some(v) => v
      | None => raise(exn)
      };
    | _ => raise(exn)
    }
  };
};

let hack_type_str_item = (f, env, stri) => {
  /*
   after generating a module type it only needs to be added to the global variable
   and to the sub environment, because if x can see f to apply, then it is a sub environment
   and if it is in a different str_item then it is below
   */
  Env_stack.push(~scope=Ctype.get_current_level(), stri.pstr_loc, env);
  let (desc, desc_signature, env) = f(env, stri);
  // switch (desc) {
  // | Tstr_value(_, [binding]) =>
  // TODO: add check to ensure they're "identical"
  //   Format.printf("%a\n%!", Printtyp.type_expr, binding.vb_expr.exp_type);
  //   Format.printf("%a\n%!", Printtyp.signature, desc_signature);
  // | _ => ()
  // };
  let (desc, desc_signature, env) = Env_stack.pop(desc, desc_signature, env);

  (desc, desc_signature, env);
};

Typecore.hack_pexp_fun := hack_pexp_fun;
Typemod.hack_type_str_item := hack_type_str_item;
