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
  Untypeast.default_mapper.structure(Untypeast.default_mapper, tstr);
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
