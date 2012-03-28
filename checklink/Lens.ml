type ('a, 'b) t = {
  get: 'a -> 'b;
  set: 'b -> 'a -> 'a;
}

let ( |- ) f g x = g (f x)

let modify l f a =
  let oldval = l.get a in
  let newval = f oldval in
  l.set newval a

let compose l1 l2 = {
  get = l2.get |- l1.get;
  set = l1.set |- modify l2
}

let _get a l = l.get a

let _set v a l = l.set v a

let _modify f l = modify l f

let (|.) = _get

let (^=) l v = fun a -> _set v a l

let (^%=) l f = _modify f l

let (|--) l1 l2 = compose l2 l1

let (--|) = compose
