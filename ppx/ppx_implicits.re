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

Driver.register_transformation(
  ~instrument=Driver.Instrument.make(~position=After, transform),
  "ppx_implicits",
);
