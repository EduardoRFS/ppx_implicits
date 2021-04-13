open Ppxlib;
let record_name = id => Printf.sprintf("hkt_magic_%d", id);
let run_name = id => Printf.sprintf("run_%d", id);

let unboxed = loc => {
  attr_name: {
    txt: "ocaml.unboxed",
    loc,
  },
  attr_loc: loc,
  attr_payload: PStr([]),
};
let make_wrapper_record = (~loc, ~id, ~wrapper_modtype, ~free_variables) => {
  // TODO: reason open F(P)
  module Ast_builder =
    Ast_builder.Make({
      let loc = loc;
    });
  open Ast_builder;

  let params =
    free_variables
    |> List.map(({txt: name, _}) =>
         (ptyp_var(name), (NoVariance, NoInjectivity))
       );

  let run_typ =
    ptyp_poly(
      [{txt: "return_type", loc}],
      ptyp_arrow(
        Nolabel,
        ptyp_package((
          {txt: Lident(wrapper_modtype), loc},
          [
            ({txt: Lident("return_type"), loc}, ptyp_var("return_type")),
            ...List.map(
                 ({txt: name, _}) =>
                   ({txt: Lident(name), loc}, ptyp_var(name)),
                 free_variables,
               ),
          ],
        )),
        ptyp_var("return_type"),
      ),
    );
  let run_label =
    label_declaration(
      ~name={txt: run_name(id), loc},
      ~mutable_=Immutable,
      ~type_=run_typ,
    );
  let name = record_name(id);
  let decl =
    type_declaration(
      ~name={txt: name, loc},
      ~params,
      ~cstrs=[],
      ~private_=Public,
      ~manifest=None,
      ~kind=Ptype_record([run_label]),
    );
  let decl = {...decl, ptype_attributes: [unboxed(loc)]};
  (decl, run_label);
};
