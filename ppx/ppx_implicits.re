open Ppxlib;
open Ocaml_common;
include Ocaml_typing_extended;
open Ocaml_typing;

let env =
  lazy(
    {
      Compmisc.init_path();
      Compmisc.initial_env();
    }
  );

let transform = str => {
  let env = Lazy.force_val(env);
  let (tstr, _, _, _) = Typemod.type_structure(env, str);
  let mapper = {
    ...Untypeast.default_mapper,
    expr: (super, expr) =>
      switch (expr.exp_attributes) {
      | [
          {
            attr_name: {txt: "untype.data", _},
            attr_payload: PStr([{pstr_desc: Pstr_eval(sexp, []), _}]),
            _,
          },
        ] => sexp
      | _ => Untypeast.default_mapper.expr(super, expr)
      },
    structure_item: (super, stri) =>
      switch (stri.str_desc) {
      | Tstr_attribute({
          attr_name: {txt: "untype.data", _},
          attr_payload: PStr([stri]),
          _,
        }) => stri
      | _ => Untypeast.default_mapper.structure_item(super, stri)
      },
    pat: (sub, pat) =>
      // TODO: upstream this
      switch (pat) {
      | {
          pat_extra: [(Typedtree.Tpat_open(_, lid, _), loc, attrs), ...rem],
          _,
        } =>
        let loc = sub.location(sub, loc);
        let attrs = sub.attributes(sub, attrs);
        Ast_helper.Pat.mk(
          ~loc,
          ~attrs,
          Ppat_open(lid, sub.pat(sub, {...pat, pat_extra: rem})),
        );
      | _ => Untypeast.default_mapper.pat(sub, pat)
      },
  };
  let str = mapper.structure(mapper, tstr);
  // Format.printf("%a\n%!", Pprintast.structure, str);
  str;
};

let transform = str => {
  let is_ocamldep = Ocaml_common.Ast_mapper.tool_name() == "ocamldep";
  if (is_ocamldep) {
    str;
  } else {
    Ppxlib.Selected_ast.To_ocaml.copy_structure(str)
    |> transform
    |> Ppxlib.Selected_ast.Of_ocaml.copy_structure;
  };
};

Driver.register_transformation(
  ~instrument=Driver.Instrument.make(~position=After, transform),
  "ppx_implicits",
);
