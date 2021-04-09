open Ppxlib;
open Ast_builder.Default;
type config = {
  exp_loc: Location.t,
  body_loc: Location.t,
  pattern_loc: Location.t,
  free_variables: list(loc(string)),
  mod_name: loc(string),
  modtype_name: loc(string),
};

let pattern_match_eq = (config, body) => {
  open Ast_builder.Default;
  let loc = config.pattern_loc;
  let name = config.mod_name;
  pexp_let(
    ~loc,
    Nonrecursive,
    [
      value_binding(
        ~loc,
        ~pat=ppat_construct(~loc, {txt: Lident("Eq"), loc}, None),
        ~expr=
          pexp_ident(
            ~loc,
            {txt: Ldot(Lident(name.txt), "eq"), loc: name.loc},
          ),
      ),
    ],
    body,
  );
};
let open_wrapper = (config, expr) => {
  let loc = config.body_loc;
  let name = config.mod_name;
  pexp_open(
    ~loc,
    open_infos(
      ~loc,
      ~override=Fresh,
      ~expr=pmod_ident(~loc, {txt: Lident(name.txt), loc: name.loc}),
    ),
    expr,
  );
};
let module_parameter = (config, aliases) => {
  let loc = config.pattern_loc;
  let modtype = {
    txt: Lident(config.modtype_name.txt),
    loc: config.modtype_name.loc,
  };
  let aliases =
    List.map(
      name => {
        let lident = {txt: Lident(name.txt), loc: name.loc};
        (lident, ptyp_constr(~loc, lident, []));
      },
      aliases,
    );
  let typ = ptyp_package(~loc, (modtype, aliases));
  let pat =
    ppat_unpack(
      ~loc,
      {txt: Some(config.mod_name.txt), loc: config.mod_name.loc},
    );
  ppat_constraint(~loc, pat, typ);
};
let transform_function = (config, body) => {
  let loc = config.exp_loc;
  let return_type = {txt: "return_type", loc: config.body_loc};
  let all_types = config.free_variables @ [return_type];

  let body =
    pattern_match_eq(
      config,
      open_wrapper(config, [%expr ([%e body]: return_type)]),
    );
  let exp_fun =
    pexp_fun(~loc, Nolabel, None, module_parameter(config, all_types), body);
  all_types
  |> List.fold_left(
       (expr, name) => pexp_newtype(~loc=name.loc, name, expr),
       exp_fun,
     );
};
