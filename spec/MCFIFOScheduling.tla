-------------------------- MODULE MCFIFOScheduling --------------------------
(***************************************************************************)
(* This is a module used for running TLC to check the specification ISpec  *)
(* of ProcessScheduler.  We need to tell TLC the values of the constant    *)
(* operators Snd and Get.  We define operators MCSnd and MCGet and         *)
(* use the configuration file to tell TLC to substitute these operators    *)
(* for Snd and Get.  We also define MCInitProcInt, which is substituted    *)
(* for InitProcInt.                                                        *)
(***************************************************************************)

EXTENDS FIFOScheduling

(***************************************************************************)
(* The operator Snd is used in specifications in conjuncts of the form     *)
(*                                                                         *)
(* (+)  Snd(p, c, tskInt, tskInt')                                       *)
(*                                                                         *)
(* to specify the new value of memInt.  For TLC to handle such a           *)
(* conjunct, the definition of Send must make (+) equal something of the   *)
(* form                                                                    *)
(*                                                                         *)
(*   tskInt' = ...                                                        *)
(*                                                                         *)
(* (A similar observation holds for Get.)  We define Send so that (+)      *)
(* equals                                                                  *)
(*                                                                         *)
(*   tskInt' = <<t, c>>                                                   *)
(*                                                                         *)
(* If we were doing serious model checking, we might try to reduce         *)
(* the state space by letting the value of memInt remain constant,         *)
(* so we would define Send so that (+) equals                              *)
(*                                                                         *)
(*   tskInt' = tskInt.                                                   *)
(***************************************************************************)
MCSnd(t, c, oldTaskInt, newTaskInt)  ==  newTaskInt = <<t, c>>
MCGet(t, c, oldTaskInt, newTaskInt) ==  newTaskInt = <<t, c>>

(***************************************************************************)
(* We define MCInitMemInt, the set of initial values of memInt, to contain *)
(* the single element <<p, NoVal>>, for an arbitrary processor p.          *)
(***************************************************************************)
MCInitTaskInt == {<<CHOOSE t \in Task : TRUE>>}

=============================================================================
\* Modification History
\* Last modified Tue Dec 11 11:52:42 BRST 2018 by ajh
\* Created Tue Dec 11 11:37:38 BRST 2018 by ajh
