type cfgInfo = {
    name: string; (* The function name *)
    start   : int;          
    size    : int;    
    blocks: cfgBlock array; (** Dominating blocks must come first *)
    successors: int list array; (* block indices *)
    predecessors: int list array;   
    mutable nrRegs: int;
    mutable regToVarinfo: Cil.varinfo array; (** Map register IDs to varinfo *)
  } 

(** A block corresponds to a statement *)
and cfgBlock = { 
    bstmt: Cil.stmt;

    (* We abstract the statement as a list of def/use instructions *)
    instrlist: instruction list;
    mutable livevars: (reg * int) list;  
    (** For each variable ID that is live at the start of the block, the 
     * block whose definition reaches this point. If that block is the same 
     * as the current one, then the variable is a phi variable *)
    mutable reachable: bool;
  }
  
and instruction = (reg list * reg list) 
  (* lhs variables, variables on rhs.  *)


and reg = int

type idomInfo = int array  (* immediate dominator *)

and dfInfo = (int list) array  (* dominance frontier *)

and oneSccInfo = {
    nodes: int list;
    headers: int list;
    backEdges: (int*int) list;
  } 

and sccInfo = oneSccInfo list 

val add_ssa_info: cfgInfo -> unit
val stronglyConnectedComponents: cfgInfo -> bool -> sccInfo 
val prune_cfg: cfgInfo -> cfgInfo
