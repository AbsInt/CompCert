(** A hash table specialized on integer keys *)
type 'a t =
  { mutable size: int;                        (* number of elements *)
    mutable data: 'a bucketlist array } (* the buckets *)

and 'a bucketlist =
    Empty
  | Cons of int * 'a * 'a bucketlist

let hash key = key land 0x3fffffff

let create initial_size =
  let s = min (max 1 initial_size) Sys.max_array_length in
  { size = 0; data = Array.make s Empty }

let clear h =
  for i = 0 to Array.length h.data - 1 do
    h.data.(i) <- Empty
  done;
  h.size <- 0

let copy h =
  { size = h.size;
    data = Array.copy h.data }

let copy_into src dest = 
  dest.size <- src.size;
  dest.data <- Array.copy src.data

let length h = h.size

let resize tbl =
  let odata = tbl.data in
  let osize = Array.length odata in
  let nsize = min (2 * osize + 1) Sys.max_array_length in
  if nsize <> osize then begin
    let ndata = Array.create nsize Empty in
    let rec insert_bucket = function
        Empty -> ()
      | Cons(key, data, rest) ->
          insert_bucket rest; (* preserve original order of elements *)
          let nidx = (hash key) mod nsize in
          ndata.(nidx) <- Cons(key, data, ndata.(nidx)) in
    for i = 0 to osize - 1 do
      insert_bucket odata.(i)
    done;
    tbl.data <- ndata;
  end

let add h key info =
  let i = (hash key) mod (Array.length h.data) in
  let bucket = Cons(key, info, h.data.(i)) in
  h.data.(i) <- bucket;
  h.size <- succ h.size;
  if h.size > Array.length h.data lsl 1 then resize h

let remove h key =
  let rec remove_bucket = function
      Empty ->
        Empty
    | Cons(k, i, next) ->
        if k = key
        then begin h.size <- pred h.size; next end
        else Cons(k, i, remove_bucket next) in
  let i = (hash key) mod (Array.length h.data) in
  h.data.(i) <- remove_bucket h.data.(i)

let remove_all h key =
  let rec remove_bucket = function
      Empty ->
        Empty
    | Cons(k, i, next) ->
        if k = key
        then begin h.size <- pred h.size; 
	  remove_bucket next end
        else Cons(k, i, remove_bucket next) in
  let i = (hash key) mod (Array.length h.data) in
  h.data.(i) <- remove_bucket h.data.(i)

let rec find_rec key = function
    Empty ->
      raise Not_found
  | Cons(k, d, rest) ->
      if key = k then d else find_rec key rest

let find h key =
  match h.data.((hash key) mod (Array.length h.data)) with
    Empty -> raise Not_found
  | Cons(k1, d1, rest1) ->
      if key = k1 then d1 else
      match rest1 with
        Empty -> raise Not_found
      | Cons(k2, d2, rest2) ->
          if key = k2 then d2 else
          match rest2 with
            Empty -> raise Not_found
          | Cons(k3, d3, rest3) ->
              if key = k3 then d3 else find_rec key rest3

let find_all h key =
  let rec find_in_bucket = function
    Empty ->
      []
  | Cons(k, d, rest) ->
      if k = key then d :: find_in_bucket rest else find_in_bucket rest in
  find_in_bucket h.data.((hash key) mod (Array.length h.data))

let replace h key info =
  let rec replace_bucket = function
      Empty ->
        raise Not_found
    | Cons(k, i, next) ->
        if k = key
        then Cons(k, info, next)
        else Cons(k, i, replace_bucket next) in
  let i = (hash key) mod (Array.length h.data) in
  let l = h.data.(i) in
  try
    h.data.(i) <- replace_bucket l
  with Not_found ->
    h.data.(i) <- Cons(key, info, l);
    h.size <- succ h.size;
    if h.size > Array.length h.data lsl 1 then resize h

let mem h key =
  let rec mem_in_bucket = function
  | Empty ->
      false
  | Cons(k, d, rest) ->
      k = key || mem_in_bucket rest in
  mem_in_bucket h.data.((hash key) mod (Array.length h.data))

let iter (f: int -> 'a -> unit) (h: 'a t) : unit =
  let rec do_bucket = function
      Empty ->
        ()
    | Cons(k, d, rest) ->
        f k d; do_bucket rest in
  let d = h.data in
  for i = 0 to Array.length d - 1 do
    do_bucket d.(i)
  done

let fold (f: int -> 'a -> 'b -> 'b) (h: 'a t) (init: 'b) =
  let rec do_bucket b accu =
    match b with
      Empty ->
        accu
    | Cons(k, d, rest) ->
        do_bucket rest (f k d accu) in
  let d = h.data in
  let accu = ref init in
  for i = 0 to Array.length d - 1 do
    accu := do_bucket d.(i) !accu
  done;
  !accu


let memoize (h: 'a t) (key: int) (f: int -> 'a) : 'a = 
  let i = (hash key) mod (Array.length h.data) in
  let rec find_rec key = function
      Empty -> addit ()
    | Cons(k, d, rest) ->
        if key = k then d else find_rec key rest
  and find_in_bucket key = function
      Empty -> addit ()
    | Cons(k1, d1, rest1) ->
        if key = k1 then d1 else
        match rest1 with
          Empty -> addit ()
        | Cons(k2, d2, rest2) ->
            if key = k2 then d2 else
            match rest2 with
              Empty -> addit () 
            | Cons(k3, d3, rest3) ->
                if key = k3 then d3 else find_rec key rest3
  and addit () = 
    let it = f key in
    h.data.(i) <- Cons(key, it, h.data.(i));
    h.size <- succ h.size;
    if h.size > Array.length h.data lsl 1 then resize h;
    it
  in
  find_in_bucket key h.data.(i)
                  
  
let tolist (h: 'a t) : (int * 'a) list = 
  fold (fun k d acc -> (k, d) :: acc) h []
