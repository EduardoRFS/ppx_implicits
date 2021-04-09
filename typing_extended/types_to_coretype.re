open Types;
open Parsetree;

module Var = {
  let n_to_b26 = n => {
    let length =
      floor(log10(26.0 +. 25.0 *. float_of_int(n)) /. log10(26.0))
      |> int_of_float;
    let bytes = Bytes.make(length, '\000');

    let rec internal = (pos, n) => {
      let remainder = n mod 26;
      let char = Char.chr(remainder + 97);
      Bytes.set(bytes, pos, char);
      pos == 0 ? () : internal(pos - 1, n / 26 - 1);
    };
    internal(length - 1, n);
    Bytes.to_string(bytes);
  };

  let last = ref(0);
  let tbl = Hashtbl.create(8);

  let get = id =>
    switch (Hashtbl.find_opt(tbl, id)) {
    | Some(v) => v
    | None =>
      let v = n_to_b26(last^);
      Hashtbl.add(tbl, id, v);
      incr(last);
      v;
    };
};

let mkloc = (~loc, v) => Location.{txt: v, loc};
let p = (~loc, desc) => {
  ptyp_desc: desc,
  ptyp_loc: loc,
  ptyp_loc_stack: [],
  ptyp_attributes: [],
};
let to_lident = path => mkloc(Untypeast.lident_of_path(path));
let rec to_coretype = (~loc, types) =>
  p(~loc, to_coretype_desc(~loc, types))
and to_coretype_desc = (~loc, types) =>
  switch (types.desc) {
  | Tvar(_) => Ptyp_var(Var.get(types.id))
  | Tarrow(label, param, body, _) =>
    let param = to_coretype(~loc, param);
    let body = to_coretype(~loc, body);
    Ptyp_arrow(label, param, body);
  | Ttuple(ts) => Ptyp_tuple(List.map(to_coretype(~loc), ts))
  | Tconstr(path, args, _) =>
    Ptyp_constr(to_lident(~loc, path), List.map(to_coretype(~loc), args))
  | Tobject(_)
  | Tfield(_)
  | Tnil => failwith("TODO: implement this")
  | Tlink(typ)
  | Tsubst(typ) => to_coretype_desc(~loc, typ)
  | Tvariant(_) => failwith("TODO: implement this")
  | Tunivar(None) => Ptyp_any // TODO: is this right?
  | Tunivar(Some(v)) => Ptyp_constr(mkloc(~loc, Longident.Lident(v)), [])
  | Tpoly(_) => failwith("TODO: implement this")
  | Tpackage(path, lids, typs) =>
    let lids = List.map(mkloc(~loc), lids);
    let typs = List.map(to_coretype(~loc), typs);
    Ptyp_package((to_lident(~loc, path), List.combine(lids, typs)));
  };
