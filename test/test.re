module type Monad = {
  type t('a);
  let return: 'a => t('a);
  let bind: (t('a), 'a => t('b)) => t('b);
};

let return = (module M: Monad, v) => M.return(v);
let bind = (module M: Monad, v, f) => M.bind(v, f);
let map = (module M: Monad, f, v) => M.bind(v, v => M.return(f(v)));
module Option = {
  include Option;
  let return = some;
};

let return_option = v => return((module Option), v);
let return_lwt = v => return((module Lwt), v);

let bind_option = (v, f) => bind((module Option), v, f);
let bind_lwt = (v, f) => bind((module Lwt), v, f);

let apply = (f, a) => f(a);
let some_6 = apply(map, (module Option), (+)(1), Some(5));

let apply_bind =
    (
      bind: ([@id M] (module Monad), M.t('b), 'b => M.t('c)) => M.t('c),
      md,
      v,
      f,
    ) =>
  bind(md, v, f);

module type Type = {type t;};
let poly = (f: ([@id T] (module Type), T.t, T.t) => T.t) => (
  f((module Int), 1, 2),
  f((module Bool), true, false),
);

let choose_fst = (module T: Type, x: T.t, _y: T.t) => x;
