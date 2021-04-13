open Ocaml_typing;
open Parsetree;
open Typedtree;
open Location;

// declaration

let (let.some) = Option.bind;

let snapshot = () => {
  let bsnap = Btype.snapshot();
  let clevels = Ctype.save_levels();
  let restore = () => {
    Btype.backtrack(bsnap);
    Ctype.set_levels(clevels);
  };
  restore;
};

// code -> hacked typechecker and transform to classic -> untype -> (ocaml typechecker -> compile)

module Env_stack = {
  let last_modtype = ref(0);
  type data = {
    binding_loc: Location.t,
    mutable source_env: Env.t,
    scope: int,
    // TODO: they need to be ordered
    mutable additional_structures:
      list(
        [
          | `Modtype(
              Typedtree.module_type_declaration,
              Types.modtype_declaration,
            )
          | `Type(Typedtree.type_declaration, Types.type_declaration)
        ],
      ),
  };
  type t = Stack.t(data);

  let stack = Stack.create();

  let push = (~scope, binding_loc, source_env) =>
    Stack.push(
      {scope, binding_loc, source_env, additional_structures: []},
      stack,
    );
  let append_modtype = (~loc, signature, env) => {
    let data = Stack.top(stack);
    let name = Printf.sprintf("HKT_Magic_%d", last_modtype^);
    incr(last_modtype);
    // copied from transl_modtype_decl_aux
    let tmty =
      Typetexp.transl_modtype^(
        // TODO: I think it shouldn't always be on source_env
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
    let (id, source_env) =
      Env.enter_modtype(
        ~scope=data.scope,
        name,
        modtype_decl,
        data.source_env,
      );
    /* this is important so that the next expression on this same structure
       can see all the types and modtypes */
    data.source_env = source_env;
    let env = Env.add_modtype(id, modtype_decl, env);
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
    data.additional_structures = [
      `Modtype((tree_modtype_decl, modtype_decl)),
      ...data.additional_structures,
    ];
    (env, name);
  };
  Printexc.record_backtrace(true);
  let append_type = (~loc, free_variables, wrapper_modtype, env) => {
    let data = Stack.top(stack);
    let id = last_modtype^;
    incr(last_modtype);

    let (decl, label_decl) =
      Codegen_wrapper_record.make_wrapper_record(
        ~loc,
        ~id,
        ~wrapper_modtype,
        ~free_variables,
      );
    let run_name = label_decl.pld_name;

    let id = Ident.create_scoped(~scope=data.scope, decl.ptype_name.txt);
    let uid = Types.Uid.mk(~current_unit=Env.get_unit_name());
    // Format.printf(
    //   "%a\n%!",
    //   Pprintast.structure,
    //   [{pstr_loc: loc, pstr_desc: Pstr_type(Nonrecursive, [decl])}],
    // );
    // TODO: this seems like a bad idea, if it mess with the scope
    let decl = Typedecl.transl_declaration(data.source_env, decl, (id, uid));
    let typ = decl.typ_type;
    data.source_env = Env.add_type(~check=true, id, typ, data.source_env);
    let env = Env.add_type(~check=true, id, typ, env);
    data.additional_structures = [
      `Type((decl, typ)),
      ...data.additional_structures,
    ];
    (env, run_name);
  };

  let pop = (desc, desc_signature, env) => {
    let data = Stack.pop(stack);
    if (data.additional_structures == []) {
      (desc, desc_signature, env);
    } else {
      let additional_structures = List.rev(data.additional_structures);
      let env =
        List.fold_left(
          (env, type_entry) =>
            switch (type_entry) {
            // TODO: add vs enter
            | `Modtype({mtd_id, _}, modtype) =>
              Env.add_modtype(mtd_id, modtype, env)
            | `Type({typ_id, _}, typ) =>
              Env.add_type(~check=false, typ_id, typ, env)
            },
          // TODO: what happens if double add?
          env,
          additional_structures,
        );
      // TODO: is it okay to use the final env for all of them?
      let additional_declarations =
        List.map(
          fun
          | `Modtype(modtype, _) => {
              str_desc: Tstr_modtype(modtype),
              str_loc: modtype.mtd_loc,
              str_env: env,
            }
          | `Type(typdecl, _) => {
              str_desc: Tstr_type(Nonrecursive, [typdecl]),
              str_loc: typdecl.typ_loc,
              str_env: env,
            },
          additional_structures,
        );
      let structure =
        additional_declarations
        @ [{str_desc: desc, str_loc: data.binding_loc, str_env: env}];
      let signature =
        List.map(
          fun
          | `Modtype({mtd_id, _}, modtype) =>
            Types.Sig_modtype(mtd_id, modtype, Exported)
          | `Type({typ_id, _}, typ) =>
            Types.Sig_type(typ_id, typ, Trec_not, Exported),
          additional_structures,
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
  let try_to_type_as_scoped_module = (mod_name, modtype, sbody) => {
    open Ctype;
    let mty_path =
      Typetexp.transl_modtype_longident^(modtype.loc, env, modtype.txt);
    let scope = Ctype.get_current_level();
    begin_def();
    let (_id, env) =
      Env.enter_module(
        ~scope=Ctype.get_current_level(),
        ~arg=true,
        mod_name,
        Mp_present,
        Mty_ident(mty_path),
        env,
      );
    // TODO: this is clearly a problem because of the type_expected stuff
    // TODO: seriously this matters because it will reject valid code
    let body = Typecore.type_expression(env, sbody);
    let ty = body.exp_type;
    end_def();
    switch (check_scope_escape(env, scope, ty)) {
    | _ => `Not_escaped
    | exception _ => `Escaped(ty)
    };
  };
  let try_to_type_as_scoped_module = (mod_name, modtype, sbody) => {
    let restore = snapshot();
    try((restore, try_to_type_as_scoped_module(mod_name, modtype, sbody))) {
    | _ => (restore, `Not_able_to_type)
    };
  };

  let type_escaped_ppat_unpack =
      (restore, ty, mod_name, mod_name_loc, modtype, modtype_loc) => {
    let mod_name = Location.{txt: mod_name, loc: mod_name_loc};
    let (free_variables, signature) =
      Codegen_wrapper_modtype.make_wrapper_signature({
        pattern_loc: spat.ppat_loc,
        param_name: mod_name,
        param_modtype: modtype,
        body_type: {
          txt: ty,
          loc: sbody.pexp_loc,
        },
      });

    // if restored before, then transforming it into a core type will fail
    restore();

    let (env, modtype_name) =
      Env_stack.append_modtype(~loc=modtype_loc, signature, env);
    let (env, run_name) =
      Env_stack.append_type(
        ~loc=modtype_loc,
        free_variables,
        modtype_name,
        env,
      );
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
            loc: modtype_loc,
          },
          run_name,
        },
        sbody,
      );
    // TODO: copy in_function and recarg here
    Typecore.type_expect(env, fn, ty_expect_explained);
  };

  switch (spat.ppat_desc) {
  | Ppat_constraint(
      {ppat_desc: Ppat_unpack({txt: Some(mod_name), loc: mod_name_loc}), _},
      {ptyp_desc: Ptyp_package((modtype, [])), ptyp_loc: modtyp_loc, _},
    ) =>
    switch (try_to_type_as_scoped_module(mod_name, modtype, sbody)) {
    | (restore, `Not_able_to_type)
    // TODO: not_escaped needs to type again? I think so, because the error message
    | (restore, `Not_escaped) =>
      restore();
      f(env, ty_expect_explained, exp_loc, l, spat, sbody);
    | (restore, `Escaped(ty)) =>
      type_escaped_ppat_unpack(
        restore,
        ty,
        mod_name,
        mod_name_loc,
        modtype,
        modtyp_loc,
      )
    }
  | _ => f(env, ty_expect_explained, exp_loc, l, spat, sbody)
  };
};

let hack_type_str_item = (f, env, stri) => {
  /*
   after generating a module type it only needs to be added to the global variable
   and to the sub environment, because if x can see f to apply, then it is a sub environment
   and if it is in a different str_item then it is below
   */
  Env_stack.push(~scope=Ctype.get_current_level(), stri.pstr_loc, env);
  let restore = snapshot();
  let (desc, desc_signature, env) =
    try(f(env, stri)) {
    | _exn =>
      open Typedtree;
      restore();
      // structure type recovery
      let loc = stri.pstr_loc;
      let desc =
        Tstr_attribute({
          attr_name: {
            loc,
            txt: "untype.data",
          },
          attr_payload: PStr([stri]),
          attr_loc: loc,
        });
      (desc, [], env);
    };
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

// application
let starts_with = (~pat, str) =>
  String.length(str) >= String.length(pat)
  && String.sub(str, 0, String.length(pat)) == pat;
let includes_hkt_applied = expr => expr.Parsetree.pmod_attributes != []; // TODO: this is dumb
let is_hkt_magic = path =>
  switch (path) {
  | Path.Pident(ident) => starts_with(~pat="HKT_Magic_", Ident.name(ident))
  | _ => false
  };

let resolve_hkt_alias = (env, path) =>
  is_hkt_magic(path)
    ? switch (Env.find_modtype(path, env).mtd_type) {
      | Some(
          Mty_signature([
            Sig_module(
              _,
              Mp_present,
              {md_type: Mty_ident(path), _},
              Trec_not,
              Exported,
            ),
            ..._,
          ]),
        ) => path
      | _ => path
      }
    : path;

let unmodified_type_package = Typecore.type_package^;
Typecore.hacked_texp_pack :=
  (
    // TODO: use lidents
    (~in_function=?, ~recarg, env, ty_expected, modexpr, path, _lidents) => {
      let.some () =
        is_hkt_magic(path) && !includes_hkt_applied(modexpr) ? Some() : None;
      let.some wrapped_mod =
        Codegen_wrap_modexpr.wrap_modexpr(env, path, modexpr);
      Some(
        Typecore.type_expect(
          ~in_function?,
          ~recarg,
          env,
          wrapped_mod,
          ty_expected,
        ),
      );
    }
  );

// types

Typetexp.hacked_ptyp_arrow :=
  ((f, env, policy, label, st1, st2) => f(env, policy, label, st1, st2));

// expression type recovery
let hacked_type_expect = (f, env, sexp, ty_expected) => {
  open Parsetree;
  open Typedtree;
  open Types;
  open Typecore;
  let restore = snapshot();
  try(f(env, sexp, ty_expected)) {
  | _ =>
    restore();
    let loc = sexp.pexp_loc;
    {
      exp_desc:
        Texp_ident(
          Path.Pident(Ident.create_local("*type-error*")),
          Location.mkloc(Longident.Lident("*type-error*"), loc),
          {
            Types.val_type: ty_expected.ty,
            val_kind: Val_reg,
            val_loc: loc,
            val_attributes: [],
            val_uid: Uid.internal_not_actually_unique,
          },
        ),
      exp_loc: loc,
      exp_extra: [],
      exp_type: ty_expected.ty,
      exp_env: env,
      exp_attributes: [
        {
          attr_name: {
            loc,
            txt: "untype.data",
          },
          attr_payload:
            PStr([{pstr_loc: loc, pstr_desc: Pstr_eval(sexp, [])}]),
          attr_loc: loc,
        },
      ],
    };
  };
};
Typecore.hacked_type_expect := hacked_type_expect;
