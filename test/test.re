module type Monad = {
  type t('a);
  let return: 'a => t('a);
  let bind: (t('a), 'a => t('b)) => t('b);
};

let return = (module M: Monad, v) => M.return(v);
let bind = (module M: Monad, v, f) => M.bind(v, f);
