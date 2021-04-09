// this is the modtype that includes the equality witness
open Ppxlib;
open Ocaml_common;
let find_free_variables = typ => {
  open Location;
  open Ast_iterator;

  let variables = ref([]);
  let iterator = {
    ...default_iterator,
    typ: (super, typ) => {
      switch (typ.ptyp_desc) {
      | Ptyp_var(name) =>
        variables := [{txt: name, loc: typ.ptyp_loc}, ...variables^]
      | _ => ()
      };
      default_iterator.typ(super, typ);
    },
  };
  iterator.typ(iterator, typ);
  variables^ |> List.sort_uniq((a, b) => String.compare(a.txt, b.txt));
};

let vars_to_constr = typ => {
  open Ocaml_common.Ast_mapper;
  let iterator = {
    ...default_mapper,
    typ: (super, t) =>
      switch (t.ptyp_desc) {
      | Ptyp_var(var) => {
          ...t,
          ptyp_desc: Ptyp_constr({txt: Lident(var), loc: t.ptyp_loc}, []),
        }
      | _ => default_mapper.typ(super, t)
      },
  };
  iterator.typ(iterator, typ);
};

type config = {
  pattern_loc: Location.t,
  param_name: loc(string),
  param_modtype: loc(Longident.t),
  body_type: loc(Types.type_expr),
};

let make_wrapper_signature =
    ({pattern_loc, param_name, param_modtype, body_type}) => {
  open Ast_builder.Default;

  // this means that most operations locs are derived from the full pattern loc
  let loc = pattern_loc;
  let source_module_alias = {
    psig_module(
      ~loc=pattern_loc,
      module_declaration(
        ~loc=pattern_loc,
        ~name={txt: Some(param_name.txt), loc: param_name.loc},
        ~type_=pmty_ident(~loc=param_modtype.loc, param_modtype),
      ),
    );
  };
  let return_signature =
    Types_to_coretype.to_coretype(~loc=body_type.loc, body_type.txt);
  let free_variables = find_free_variables(return_signature);
  let free_variables_alias =
    free_variables
    |> List.map(name => {
         let loc = name.loc;
         let decl =
           type_declaration(
             ~loc,
             ~name,
             ~params=[],
             ~cstrs=[],
             ~kind=Ptype_abstract,
             ~private_=Public,
             ~manifest=None,
           );
         psig_type(~loc, Nonrecursive, [decl]);
       });

  let return_type_equality = [%sig:
    type return_type;
    type eq('a, 'b) =
      | Eq: eq('a, 'a);
    let eq: eq(return_type, [%t vars_to_constr(return_signature)])
  ];
  let signature =
    [source_module_alias, ...free_variables_alias] @ return_type_equality;
  (free_variables, signature);
};
