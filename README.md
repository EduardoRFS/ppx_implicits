# ppx_implicits

Only explicits implemented, for now.

## How to use

### Requirements

- ocaml@4.12.x

### esy

```sh
esy add ppx_implicits@EduardoRFS/ppx_implicits#HASH_HERE
```

### opam

```sh
opam pin ppx_implicits https://github.com/EduardoRFS/ppx_implicits.git#HASH_HERE
```

### dune

Add it as `(preprocess (staged_pps ppx_implicits))`, like:

```dune
(executable
 (name test)
 (preprocess
  (staged_pps ppx_implicits)))
```

### How it works?

A typer hacked and some fancy elaboration, you will be able to notice by hovering over declarations with merlin.

### Examples

For more examples you can look on [test/test.re](https://github.com/EduardoRFS/ppx_implicits/blob/branch-private-please-dont-look-here/test/test.re)

```ocaml
module type Monad = sig
  type 'a t
  val return : 'a -> 'a t
  val bind : 'a t -> ('a -> 'b t) -> 'b t
end
module Option = struct
  include Option
  let return = some
end

let bind (module M : Monad) v f = M.bind v f
let bind_option v f = bind (module Option) v f
let some_6 =
  bind
    (module Option)
    (Some 5)
    (fun v -> Some (v + 1))
```
