open Parsetree;
open Location;

let (let.some) = Option.bind;

let load_data_from_hkt = (env, path) => {
  let modtype = Env.find_modtype_expansion(path, env) |> Mtype.scrape(env);
  switch (modtype) {
  | Mty_signature([
      Sig_module(ident, Mp_present, _, Trec_not, Exported),
      ...remaining,
    ]) =>
    switch (List.rev(remaining)) {
    | [
        Sig_value(
          eq_ident,
          {
            val_type: {
              desc:
                Types.Tconstr(
                  typ_path,
                  [{desc: Tconstr(return_type_path, [], _), _}, return_typ],
                  _,
                ),
              _,
            },
            _,
          },
          Exported,
        ),
        ..._,
      ]
        when
          Ident.name(eq_ident) == "eq"
          && Path.name(typ_path) == "eq"
          && Path.name(return_type_path) == "return_type" =>
      let aliases =
        remaining
        |> List.filter_map(
             fun
             | Types.Sig_type(
                 ident,
                 {
                   type_params: [],
                   type_kind: Type_abstract,
                   type_manifest: None,
                   _,
                 },
                 _,
                 Exported,
               )
                 when Ident.name(ident) != "return_type" =>
               Some(Ident.name(ident))
             | _ => None,
           );
      Some((ident, aliases, return_typ));
    | _ => None
    }
  | _ => None
  };
};

let wrap_modexpr = (env, path, modexpr) => {
  open Ppxlib.Ast_builder.Default;
  let loc = modexpr.pmod_loc;
  let.some (ident, typ_aliases, return_typ) = load_data_from_hkt(env, path);
  let return_typ = Types_to_coretype.to_coretype(~loc, return_typ);
  let typ =
    ptyp_package(
      ~loc,
      (
        {txt: Untypeast.lident_of_path(path), loc},
        (
          typ_aliases
          |> List.map(ident => {
               let lid = Location.{txt: Longident.Lident(ident), loc};
               (lid, ptyp_constr(~loc, lid, []));
             })
        )
        @ [({txt: Lident("return_type"), loc}, return_typ)],
      ),
    );

  let modname = {txt: Ident.name(ident), loc};
  let modname_opt = {...modname, txt: Some(modname.txt)};
  let md =
    pstr_module(
      ~loc,
      module_binding(
        ~loc,
        ~name=modname_opt,
        ~expr=pmod_ident(~loc, {...modname, txt: Lident(modname.txt)}),
      ),
    );
  let typs =
    (
      typ_aliases
      |> List.map(name =>
           (name, ptyp_constr(~loc, {txt: Lident(name), loc}, []))
         )
    )
    @ [("return_type", return_typ)]
    |> List.map(((name, manifest)) =>
         pstr_type(
           ~loc,
           Nonrecursive,
           [
             type_declaration(
               ~loc,
               ~name={txt: name, loc},
               ~params=[],
               ~cstrs=[],
               ~kind=Ptype_abstract,
               ~private_=Public,
               ~manifest=Some(manifest),
             ),
           ],
         )
       );
  let eq =
    pstr_value(
      ~loc,
      Nonrecursive,
      [
        value_binding(
          ~loc,
          ~pat=pvar(~loc, "eq"),
          ~expr=pexp_construct(~loc, {txt: Lident("Eq"), loc}, None),
        ),
      ],
    );
  let str =
    [
      md,
      [%stri
        type eq('a, 'b) =
          | Eq: eq('a, 'a)
      ],
    ]
    @ typs
    @ [eq];
  let packed =
    pexp_pack(
      ~loc,
      {
        ...pmod_structure(~loc, str),
        pmod_attributes: [
          attribute(
            ~loc,
            ~name={loc, txt: "hkt.applied"},
            ~payload=PStr([]),
          ),
        ],
      },
    );
  let packed_typed = pexp_constraint(~loc, packed, typ);
  let expr =
    pexp_letmodule(
      ~loc,
      {txt: Some(Ident.name(ident)), loc},
      modexpr,
      packed_typed,
    );
  Some(
    typ_aliases
    |> List.fold_left(
         (expr, typ) => pexp_newtype(~loc, {txt: typ, loc}, expr),
         expr,
       ),
  );
};
let wrap_modexpr = (env, path, modexpr) =>
  wrap_modexpr(
    env,
    path,
    switch (
      Ppxlib.Selected_ast.Of_ocaml.copy_expression({
        pexp_desc: Pexp_pack(modexpr),
        pexp_loc: modexpr.pmod_loc,
        pexp_loc_stack: [],
        pexp_attributes: [],
      }).
        pexp_desc
    ) {
    | Pexp_pack(modexpr) => modexpr
    | _ => assert(false)
    },
  )
  |> Option.map(Ppxlib.Selected_ast.To_ocaml.copy_expression);
