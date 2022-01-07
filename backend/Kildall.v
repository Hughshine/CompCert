(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*          Xavier Leroy, INRIA Paris-Rocquencourt                     *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique.  All rights reserved.  This file is distributed       *)
(*  under the terms of the INRIA Non-Commercial License Agreement.     *)
(*                                                                     *)
(* *********************************************************************)

(** Solvers for dataflow inequations. *)

Require Import Coqlib.
Require Import Iteration.
Require Import Maps.
Require Import Lattice.

(* To avoid useless definitions of inductors in extracted code. *)
Local Unset Elimination Schemes.
Local Unset Case Analysis Schemes.
(** 
   Transfer function 在这个证明里有什么地位？Transfer function的性质？
*)
(** A forward dataflow problem is a set of inequations of the form
- [X(s) >= transf n X(n)]
  if program point [s] is a successor of program point [n]
- [X(n) >= a]
  if [n] is an entry point and [a] its minimal approximation.

The unknowns are the [X(n)], indexed by program points (e.g. nodes in the
CFG graph of a RTL function).  They range over a given ordered set that
represents static approximations of the program state at each point.
The [transf] function is the abstract transfer function: it computes an
approximation [transf n X(n)] of the program state after executing instruction
at point [n], as a function of the approximation [X(n)] of the program state
before executing that instruction.

Symmetrically, a backward dataflow problem is a set of inequations of the form
- [X(n) >= transf s X(s)]
  if program point [s] is a successor of program point [n]
- [X(n) >= a]
  if [n] is an entry point and [a] its minimal approximation.

The only difference with a forward dataflow problem is that the transfer
function [transf] now computes the approximation before a program point [s]
from the approximation [X(s)] after point [s].

This file defines three solvers for dataflow problems.  The first two
solve (optimally) forward and backward problems using Kildall's worklist
algorithm.  They assume that the unknowns range over a semi-lattice, that is,
an ordered type equipped with a least upper bound operation.

The last solver corresponds to propagation over extended basic blocks:
it returns approximate solutions of forward problems where the unknowns
range over any ordered type having a greatest element [top].  It simply
sets [X(n) = top] for all merge points [n], that is, program points having
several predecessors.  This solver is useful when least upper bounds of
approximations do not exist or are too expensive to compute. *)

(** * Solving forward dataflow problems using Kildall's algorithm *)

(** A forward dataflow solver has the following generic interface.
  Unknowns range over the type [L.t], which is equipped with
  semi-lattice operations (see file [Lattice]).  *)

Module Type DATAFLOW_SOLVER.

  Declare Module L: SEMILATTICE.

  (** [fixpoint successors transf ep ev] is the solver.
    It returns either an error or a mapping from program points to
    values of type [L.t] representing the solution.  [successors]
    is a finite map returning the list of successors of the given program
    point. [transf] is the transfer function, [ep] the entry point,
    and [ev] the minimal abstract value for [ep]. *)

  Parameter fixpoint:
    forall {A: Type} (code: PTree.t A) (successors: A -> list positive)
           (transf: positive -> L.t -> L.t)
           (ep: positive) (ev: L.t),
    option (PMap.t L.t).
    Compute fixpoint.

  (** The [fixpoint_solution] theorem shows that the returned solution,
    if any, satisfies the dataflow inequations. *)

  Axiom fixpoint_solution:
    forall A (code: PTree.t A) successors transf ep ev res n instr s,
    fixpoint code successors transf ep ev = Some res ->
    code!n = Some instr -> In s (successors instr) ->
    (forall n, L.eq (transf n L.bot) L.bot) ->
    L.ge res!!s (transf n res!!n).

  (** The [fixpoint_entry] theorem shows that the returned solution,
    if any, satisfies the additional constraint over the entry point. *)

  Axiom fixpoint_entry:
    forall A (code: PTree.t A) successors transf ep ev res,
    fixpoint code successors transf ep ev = Some res ->
    L.ge res!!ep ev.

  (** Finally, any property that is preserved by [L.lub] and [transf]
      and that holds for [L.bot] also holds for the results of
      the analysis. *)

  Axiom fixpoint_invariant:
    forall A (code: PTree.t A) successors transf ep ev
           (P: L.t -> Prop),
    P L.bot ->
    (forall x y, P x -> P y -> P (L.lub x y)) ->
    (forall pc instr x, code!pc = Some instr -> P x -> P (transf pc x)) ->
    P ev ->
    forall res pc,
    fixpoint code successors transf ep ev = Some res ->
    P res!!pc.

End DATAFLOW_SOLVER.

(** Kildall's algorithm manipulates worklists, which are sets of CFG nodes
  equipped with a ``pick next node to examine'' operation.
  The algorithm converges faster if the nodes are chosen in an order
  consistent with a reverse postorder traversal of the CFG.
  For now, we parameterize the dataflow solver over a module
  that implements sets of CFG nodes. *)

Module Type NODE_SET. (** pick 的方式由 NODESET 自行决定，它并不影响正确性，只影响效率*)

  (** 实现NODE_SET的抽象的数据类型 *)
  Parameter t: Type. 
  (** 该类型有一个常量empty，它满足empty_spec, 即empty中不存在任何node*)
  Parameter empty: t. 
  (** 对node set增加一个结点的操作，满足add_spec，即若增加一个结点n后，可以在里面找到结点n'，那么或者n'是刚刚被加入的结点n，或者n'加入前就存在；反向也成立*)
  Parameter add: positive -> t -> t. 
  (** 返回结点的标号，与结果的node set. 新的node set的元素不比之前的多. 被pick出来的结点在之前存在. 
  （允许pick是contains的实现）*)
  Parameter pick: t -> option (positive * t).
  (** 将code所有结点加入nodeset; 不保证加了更多的结点 *)
  Parameter all_nodes: forall {A: Type}, PTree.t A -> t.

  Parameter In: positive -> t -> Prop.
  Axiom empty_spec:
    forall n, ~In n empty.

  (** 为什么这样子定义add_spec还不清楚，可能这样子就是归纳式的定义了；
      应该是要将任意的In 和 刚add的结点 之间创立关系*)
  Axiom add_spec:
    forall n n' s, In n' (add n s) <-> n = n' \/ In n' s.
  
  (** pick n的结果，与 In n 的关系*)
  Axiom pick_none:
    forall s n, pick s = None -> ~In n s. (** TODO: 为什么没有反向 *)

  (** pick 之前的set 与 pick 之后 set的关系：除了被pick出的那个元素，别的元素都在新的集合里；被pick的那个元素，和新集合中所有的元素，也都在之前的集合里*)
  (** 但是没有说，pick的元素，就不会再pick 到了，这会不会影响单调性... 进一步是算法的终止性... TODO 
      或者可能就是不需要那么强吧.... 
  *)
  Axiom pick_some:
    forall s n s', pick s = Some(n, s') -> 
    forall n', In n' s <-> n = n' \/ In n' s'.
  Axiom all_nodes_spec:
    forall A (code: PTree.t A) n instr,
    code!n = Some instr -> In n (all_nodes code).

End NODE_SET.

(** Reachability in a control-flow graph. *)

Section REACHABLE.

Context {A: Type} (code: PTree.t A) (successors: A -> list positive).

(** 这里的reachable不能保证可达链的最后一个处于code中 *)
Inductive reachable: positive -> positive -> Prop :=
  | reachable_refl: forall n, reachable n n  (** 自反这里，并不要求结点是在code 中的；结合reachable_left，也就是左结合时要求前驱在代码中（因为successor 是关于指令的函数，而不是关于positive的） *)
  | reachable_left: forall n1 n2 n3 i,
      code!n1 = Some i -> In n2 (successors i) -> reachable n2 n3 -> 
      reachable n1 n3.

Scheme reachable_ind := Induction for reachable Sort Prop.

Lemma reachable_trans:
  forall n1 n2, reachable n1 n2 -> forall n3, reachable n2 n3 -> reachable n1 n3.
Proof.
  induction 1; intros.
- auto.
- econstructor; eauto.
Qed.

(** TODO: 注意这里从code取某个结点的操作，是直接 = Some i.
    因为reachable n1 n2 并不能保证code!n2 不是None.
*)
Lemma reachable_right:
  forall n1 n2 n3 i,
  reachable n1 n2 -> code!n2 = Some i -> In n3 (successors i) ->
  reachable n1 n3.  (** 这里其实也不能保证 n3在代码中 *)
Proof.
  intros. apply reachable_trans with n2; auto. econstructor; eauto. constructor.
Qed.

End REACHABLE.

(** We now define a generic solver for forward dataflow inequations
  that works over any semi-lattice structure. *)

(** 一个Solver被实例化，需要Fact的类型（即LAT），一个结点集合的实现类型（自行确定遍历方式） *)
(** 它需要证明自己满足Module Type里定义的那些公理 *)
Module Dataflow_Solver (LAT: SEMILATTICE) (NS: NODE_SET) <:
                          DATAFLOW_SOLVER with Module L := LAT.

Module L := LAT.

Section Kildall.

Context {A: Type}.
Variable code: PTree.t A.
Variable successors: A -> list positive.
Variable transf: positive -> L.t -> L.t.

(** The state of the iteration has three components:
- [aval]: A mapping from program points to values of type [L.t] representing
  the candidate solution found so far.
- [worklist]: A worklist of program points that remain to be considered.
- [visited]: A set of program points that were visited already (** TODO: visited 这里究竟在证明中起到什么作用？ *)
  visited: 某个结点加入过worklist（而不是被poll过）
  (i.e. put on the worklist at some point in the past).

Only the first two components are computationally relevant.  The third
is a ghost variable used only for stating and proving invariants.
For this reason, [visited] is defined at sort [Prop] so that it is
erased during program extraction.
*)

Record state : Type :=
  mkstate { aval: PTree.t L.t; worklist: NS.t; visited: positive -> Prop }.

(** TODO: 取结果可能取到空，究竟意味着什么？ 对证明来说，这部分信息的缺失，从何种角度不影响最终的正确性？*)
Definition abstr_value (n: positive) (s: state) : L.t :=
  match s.(aval)!n with
  | None => L.bot
  | Some v => v
  end.
(** TODO: 不同定理对最终的正确性究竟的贡献是什么？ 为什么要这么拆解？ *)
(** TODO: transf function在solver的正确性中究竟有何种意义？
    如果我要改成block based：
    1. 我要提供什么形式的结果？
    2. transf function 需要如何调整？ 需要满足什么？
    3. 似乎有两种处理方案，
      1. solver出来的结果直接就带有block中每个inst的结果
      2. solver出来的结果只有每个block的out（in？），需要再过一遍transfer
    * 我会需要transf具有一些额外的性质吗
*)
(** Kildall's algorithm, in pseudo-code, is as follows:
<<
    while worklist is not empty, do
        extract a node n from worklist
        compute out = transf n aval[n]
        for each successor s of n:
            compute in = lub aval[s] out
            if in <> aval[s]:
                aval[s] := in
                worklist := worklist union {s}
                visited := visited union {s}
            end if
        end for
    end while
    return aval
>>
*)

(** [propagate_succ] corresponds, in the pseudocode,
  to the body of the [for] loop iterating over all successors. *)

(** 能走到这里的结点n，都是在cfg上的【在输入结点都是cfg中结点的前提下】；
    TODO，问，算法是怎么处理输入不在cfg的情况的？【这部分性质，应该不是propagate_succ去关心的】*)
Definition propagate_succ (s: state) (out: L.t) (n: positive) :=
  match s.(aval)!n with
  | None =>
      {| aval := PTree.set n out s.(aval);  (** 之前没记录过这个后继节点的结果，那么n的out就是这个结点的in*)
         worklist := NS.add n s.(worklist); 
         visited := fun p => p = n \/ s.(visited) p |}  (** 算作该结点已经加入过worklist *)
  | Some oldl =>
      let newl := L.lub oldl out in
      if L.beq oldl newl
      then s
      else {| aval := PTree.set n newl s.(aval);
              worklist := NS.add n s.(worklist);
              visited := fun p => p = n \/ s.(visited) p |} (** 算作该结点已经加入过worklist *)
  end.

(** [propagate_succ_list] corresponds, in the pseudocode,
  to the [for] loop iterating over all successors. *)

Fixpoint propagate_succ_list (s: state) (out: L.t) (succs: list positive)
                             {struct succs} : state :=
  match succs with
  | nil => s
  | n :: rem => propagate_succ_list (propagate_succ s out n) out rem
  end.

(** [step] corresponds to the body of the outer [while] loop in the
  pseudocode. *)

(** step 不影响aval，只是会将worklist改成rem  *)
Definition step (s: state) : PMap.t L.t + state :=
  match NS.pick s.(worklist) with
  | None =>
      inl _ (L.bot, s.(aval)) (** 由PTree构造PMap, 后者比前者就多一个default... *)
  | Some(n, rem) => (** 一般迭代过程 *)
      match code!n with   
      | None => (** 若查不到该节点，当作它不存在 *)
          inr _ {| aval := s.(aval); worklist := rem; visited := s.(visited) |}
      | Some instr => (** 根据自己的in（应当是存在的），算出out，试着propagate到每个后继 *)
          inr _ (propagate_succ_list
                  {| aval := s.(aval); worklist := rem; visited := s.(visited) |}
                  (transf n (abstr_value n s))  
                  (successors instr))
      end
  end.

(** The whole fixpoint computation is the iteration of [step] from
  an initial state. *)

Definition fixpoint_from (start: state) : option (PMap.t L.t) :=
  PrimIter.iterate _ _ step start.  (** 迭代上限是在Iter.v定义的，一个很大的positive *)

(** There are several ways to build the initial state.  For forward
  dataflow analyses, the initial worklist is the function entry point,
  and the initial mapping sets the function entry point to the given
  abstract value, and leaves unset all other program points, which
  corresponds to [L.bot] initial abstract values. *)

Definition start_state (enode: positive) (eval: L.t) :=
  {| aval := PTree.set enode eval (PTree.empty L.t);  
  (** 并不检查entry node是否在code中，直接set它的下限分析结果（应该一定是L.bot? ）*)
  (** 并将它加入worklist（visited也同步记录） *)
    worklist := NS.add enode NS.empty;
    visited := fun n => n = enode |}.

Definition fixpoint (enode: positive) (eval: L.t) :=
  fixpoint_from (start_state enode eval).

(** For backward analyses (viewed as forward analyses on the reversed CFG),
  the following two variants are more useful.  Both start with an
  empty initial mapping, where all program points start at [L.bot].
  The first initializes the worklist with a given set of entry points
  in the reversed CFG.  (See the backward dataflow solver below for
  how this list is computed.)  The second start state construction
  initializes the worklist with all program points of the given CFG. *)

Definition start_state_nodeset (enodes: NS.t) :=
  {| aval := PTree.empty L.t;  (** 对于用一堆enodes做初始化的情况，没有去理会aval，可能是无所谓吧.. 因为从result会最后取出默认值？ ==> fixpoint_entry要求的是enode，而不是enodes【也就是好像没有fixpoint_nodeset_entries】，这里会怎么被处理，TODO*)
     worklist := enodes;
     visited := fun n => NS.In n enodes |}.

Definition fixpoint_nodeset (enodes: NS.t) := 
  fixpoint_from (start_state_nodeset enodes).

Definition start_state_allnodes :=  (** *_nodeset和 code 无关，allnodes和code有关（将所有code中的结点加入）*)
  {| aval := PTree.empty L.t;
     worklist := NS.all_nodes code;
     visited := fun n => exists instr, code!n = Some instr |}.

Definition fixpoint_allnodes :=
  fixpoint_from start_state_allnodes.

(** ** Characterization of the propagation functions *)

Inductive optge: option L.t -> option L.t -> Prop :=
  | optge_some: forall l l',
      L.ge l l' -> optge (Some l) (Some l')
  | optge_none: forall ol,
      optge ol None.

Remark optge_refl: forall ol, optge ol ol.
Proof. destruct ol; constructor. apply L.ge_refl; apply L.eq_refl. Qed.

Remark optge_trans: forall ol1 ol2 ol3, optge ol1 ol2 -> optge ol2 ol3 -> optge ol1 ol3.
Proof.
  intros. inv H0.
  inv H. constructor. eapply L.ge_trans; eauto.
  constructor.
Qed.

Remark optge_abstr_value:
  forall st st' n,
  optge st.(aval)!n st'.(aval)!n ->
  L.ge (abstr_value n st) (abstr_value n st').
Proof.
  intros. unfold abstr_value. inv H. auto. apply L.ge_bot.
Qed.


(** propagate_succ 做的事情：根据前驱节点的out，尝试改变aval[n]（涉及aval和visited两处修改）*)
Lemma propagate_succ_charact:
  forall st out n,
  let st' := propagate_succ st out n in 
     optge st'.(aval)!n (Some out)  (** 这个程序点的AI单调（相对于一个前驱的out）*)
  /\ (forall s, n <> s -> st'.(aval)!s = st.(aval)!s)  (** 只影响这一个节点 *)
  /\ (forall s, optge st'.(aval)!s st.(aval)!s) (** 每个程序点的AI单调（相对于它以前） *)
  /\ (NS.In n st'.(worklist) \/ st'.(aval)!n = st.(aval)!n) (** 这个节点或者在worklist，或者它没有发生改变 *)
  /\ (forall n', NS.In n' st.(worklist) -> NS.In n' st'.(worklist)) (** 之前在worklist中的节点，之后仍然在（这一步不会缩小worklist） *)
  /\ (forall n', NS.In n' st'.(worklist) -> n' = n \/ NS.In n' st.(worklist))  (** 新的worklist中的节点，或者是之前在的节点，或者是这个新加入的后继 *)
  /\ (forall n', st.(visited) n' -> st'.(visited) n') (** 旧状态的visited项，被保持 *)
  /\ (forall n', st'.(visited) n' -> NS.In n' st'.(worklist) \/ st.(visited) n')  (** 新状态的visited项中包含的节点，或者是旧状态就记录被访问的，或者是在worklist中，未来会被访问 *)
  /\ (forall n', st.(aval)!n' = None -> st'.(aval)!n' <> None -> st'.(visited) n'). (** 若产生了新的分析结果（之前未初始化），那么新的状态一定记录了对这个程序点有访问 *)
Proof.
  unfold propagate_succ; intros; simpl.
  destruct st.(aval)!n as [v|] eqn:E;
  [predSpec L.beq L.beq_correct v (L.lub v out) | idtac].  (** 这两句话在做什么 *)
- (* already there, unchanged *)
  repeat split; intros.
  + rewrite E. constructor. eapply L.ge_trans. apply L.ge_refl. apply H; auto. apply L.ge_lub_right.
  + apply optge_refl.
  + right; auto.
  + auto.
  + auto.
  + auto.
  + auto.
  + congruence.
- (* already there, updated *)
  simpl; repeat split; intros.
  + rewrite PTree.gss. constructor. apply L.ge_lub_right.
  + rewrite PTree.gso by auto. auto.
  + rewrite PTree.gsspec. destruct (peq s n).
    subst s. rewrite E. constructor. apply L.ge_lub_left.
    apply optge_refl.
  + rewrite NS.add_spec. auto.
  + rewrite NS.add_spec. auto.
  + rewrite NS.add_spec in H0. intuition.
  + auto.
  + destruct H0; auto. subst n'. rewrite NS.add_spec; auto.
  + rewrite PTree.gsspec in H1. destruct (peq n' n). auto. congruence.
- (* not previously there, updated *)
  simpl; repeat split; intros.
  + rewrite PTree.gss. apply optge_refl.
  + rewrite PTree.gso by auto. auto.
  + rewrite PTree.gsspec. destruct (peq s n).
    subst s. rewrite E. constructor.
    apply optge_refl.
  + rewrite NS.add_spec. auto.
  + rewrite NS.add_spec. auto.
  + rewrite NS.add_spec in H. intuition.
  + auto.
  + destruct H; auto. subst n'. rewrite NS.add_spec. auto.
  + rewrite PTree.gsspec in H0. destruct (peq n' n). auto. congruence.
Qed.

Lemma propagate_succ_list_charact:
  forall out l st,
  let st' := propagate_succ_list st out l in
     (forall n, In n l -> optge st'.(aval)!n (Some out))  
    (** 对于迭代的所有后继，它的分析结果都比前驱的out要大 *)
  /\ (forall n, ~In n l -> st'.(aval)!n = st.(aval)!n)
    (** 对于不在后继list中的节点，前后的分析结果一致 *)
  /\ (forall n, optge st'.(aval)!n st.(aval)!n)
    (** 每个程序点的AI单调 *)
  /\ (forall n, NS.In n st'.(worklist) \/ st'.(aval)!n = st.(aval)!n)
    (** 每个程序点，它或者在worklist中，或者它的值没有改变 *)
  /\ (forall n', NS.In n' st.(worklist) -> NS.In n' st'.(worklist))
    (** 如果一个节点之前在worklist中，那它之后也在worklist中 -- 这一步未缩小work list *)
  /\ (forall n', NS.In n' st'.(worklist) -> In n' l \/ NS.In n' st.(worklist))
    (** 如果一个节点结果的worklist中，那意味着它或者是succs中的节点，或者之前就在worklist *)
  /\ (forall n', st.(visited) n' -> st'.(visited) n')
    (** 之前访问过的，之后也访问过 *)
  /\ (forall n', st'.(visited) n' -> NS.In n' st'.(worklist) \/ st.(visited) n')
    (** 之后有访问标记的节点，意味着它或者之前访问过，或者在结果的worklist中，会在未来被访问*)
  /\ (forall n', st.(aval)!n' = None -> st'.(aval)!n' <> None -> st'.(visited) n').
    (** 这一轮结果更新过的（之前是undefine）的节点，它一定被置上了访问标记 *)
Proof.
  induction l; simpl; intros.
- repeat split; intros.
  + contradiction.
  + apply optge_refl.
  + auto.
  + auto.
  + auto.
  + auto.
  + auto.
  + congruence.
- generalize (propagate_succ_charact st out a).
  set (st1 := propagate_succ st out a).
  intros (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9).
  generalize (IHl st1).
  set (st2 := propagate_succ_list st1 out l).
  intros (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8 & B9). clear IHl.
  repeat split; intros.
  + destruct H.
    * subst n. eapply optge_trans; eauto.
    * auto.
  + rewrite B2 by tauto. apply A2; tauto.
  + eapply optge_trans; eauto.
  + destruct (B4 n). auto.
    destruct (peq n a).
    * subst n. destruct A4. left; auto. right; congruence.
    * right. rewrite H. auto.
  + eauto.
  + exploit B6; eauto. intros [P|P]. auto.
    exploit A6; eauto. intuition.
  + eauto.
  + specialize (B8 n'); specialize (A8 n'). intuition.
  + destruct st1.(aval)!n' eqn:ST1.
    apply B7. apply A9; auto. congruence.
    apply B9; auto.
Qed.

(** Characterization of [fixpoint_from]. *)

Inductive steps: state -> state -> Prop := (** step -> steps *)
  | steps_base: forall s, steps s s
  | steps_right: forall s1 s2 s3, steps s1 s2 -> step s2 = inr s3 -> steps s1 s3.

Scheme steps_ind := Induction for steps Sort Prop.  (** 这一步和Coq进行自动化推理的机制有关，需要看CoqArt中这部分，TODO*)

(** 能得到结果，意味着算法会在执行有限步后停下，worklist为空
    （最终返回的结果是只取了aval，但是取之前的state的性质还需要说明。）
*)
Lemma fixpoint_from_charact:
  forall start res,
  fixpoint_from start = Some res ->
  exists st, steps start st /\ NS.pick st.(worklist) = None /\ res = (L.bot, st.(aval)).
Proof. 
  unfold fixpoint; intros.
  eapply (PrimIter.iterate_prop _ _ step
              (fun st => steps start st)
              (fun res => exists st, steps start st /\ NS.pick (worklist st) = None /\ res = (L.bot, aval st))); eauto.
  intros. destruct (step a) eqn:E.
  exists a; split; auto.
  unfold step in E. destruct (NS.pick (worklist a)) as [[n rem]|].
  destruct (code!n); discriminate.
  inv E. auto.
  eapply steps_right; eauto.
  constructor.
Qed.

(** ** Monotonicity properties *)

(** We first show that the [aval] and [visited] parts of the state
evolve monotonically:
- at each step, the values of the [aval[n]] either remain the same or
  increase with respect to the [optge] ordering;
- every node visited in the past remains visited in the future.
*)
(** 前面说明了若算法终止得到结果，那么最终结果（和最后一个状态）的性质：
    通过steps start得到了这个最后状态，它的worklist为空，res来源于这个状态的分析结果。【描述了开始状态和最终状态的样子】
    现在要尝试建立两者间的关系（主要是（每一个fact）分析结果的evolve）：通过说明step的性质 *)
(** 1. 单步step的单调性 *)
(** 先推理一个简单的性质：状态中每一个节点的相关信息，在（单步）step前后的关系（单调） *)
Lemma step_incr:
  forall n s1 s2, step s1 = inr s2 ->
  optge s2.(aval)!n s1.(aval)!n /\ (s1.(visited) n -> s2.(visited) n). (** aval 一定会变大*)
Proof.
  unfold step; intros.
  destruct (NS.pick (worklist s1)) as [[p rem] | ]; try discriminate.
  destruct (code!p) as [instr|]; inv H.
  + generalize (propagate_succ_list_charact
                     (transf p (abstr_value p s1))
                     (successors instr)
                     {| aval := aval s1; worklist := rem; visited := visited s1 |}).
      simpl.
      set (s' := propagate_succ_list {| aval := aval s1; worklist := rem; visited := visited s1 |}
                    (transf p (abstr_value p s1)) (successors instr)).
      intros (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9).
      auto.
  + split. apply optge_refl. auto.
Qed.

(** 2. 多步steps的单调性，它考察的是每一个fact在迭代中的变化关系 *)
(** 先推理一个简单的性质：状态中每一个节点的相关信息，在（多步）steps前后的关系（单调） *)
Lemma steps_incr: 
  forall n s1 s2, steps s1 s2 ->
  optge s2.(aval)!n s1.(aval)!n /\ (s1.(visited) n -> s2.(visited) n).
Proof.
  induction 1.
- split. apply optge_refl. auto.
- destruct IHsteps. exploit (step_incr n); eauto. intros [P Q].
  split. eapply optge_trans; eauto. eauto.
Qed.

(** ** Correctness invariant *)
(** 现在可以讨论正确性的build block，
    —— 这个迭代算法，怎么与定义的结果inequation联系起来的：
    worklist中的entry是所有的访问了的，但还没有达成正确性结果等式的那些节点（每个状态都是goodstate） *)
(** The following invariant is preserved at each iteration of Kildall's
  algorithm: for all visited program point [n], either
  [n] is in the worklist, or the inequations associated with [n]
  ([aval[s] >= transf n aval[n]] for all successors [s] of [n])
  hold.  In other terms, the worklist contains all nodes that were
  visited but do not yet satisfy their inequations.

  The second part of the invariant shows that nodes that already have
  an abstract value associated with them have been visited. *)
(** stable 和 defined 分别关注两个方向，一个是“被访问过”与分析结果的关系，一个是有分析结果和“被访问过”的关系*)
(** step做两件事：
    1. poll entry
    2. propagate new abstract value to successors  
good state 的两个性质，stable 和worklist有关，它必须在两件事都做完才能维持；
defined 是比较朴素地正确
    * 似乎没有保证worklist和分析结果是统一的
*)
Record good_state (st: state) : Prop := {
  (** 每一个被访问过的结点（被加入过worklist即被访问过），如果它此时不在worklist中，那么它相对于它的后继目前是有inequation关系的*)
  gs_stable: forall n,
    st.(visited) n -> 
    NS.In n st.(worklist) \/ 
    (forall i s, 
     code!n = Some i -> In s (successors i) ->
     optge st.(aval)!s (Some (transf n (abstr_value n st))));
  (** 如果某个结点有分析结果，那么它一定被访问过（加入过worklist） *)  (** 但是visited 不一定有结果 *)
  gs_defined: forall n v,
    st.(aval)!n = Some v -> st.(visited) n 
}.

(** We show that the [step] function preserves this invariant. *)
(** step维持good_state invariant（这里没有显式的step，但实际已经是了：取出一个元素，然后propagate_succ_list） 
    也就是 good state st -> step st = st' -> good state st'
    step_state_good 是在说 取出来的结点在code中的情况，也就是正常情况（worklist entry是不是在successor这是不确定的，也就是code和successor似乎是没有建立关系的）
    step_state_good_2 是在说 取出来的结点不再code中，也就是step的另一个分支
    两个合起来，就是完整的 step good state
*)
Lemma step_state_good:
  forall st pc rem instr,
  NS.pick st.(worklist) = Some (pc, rem) ->
  code!pc = Some instr ->
  good_state st ->
  good_state (propagate_succ_list (mkstate st.(aval) rem st.(visited))
                                  (transf pc (abstr_value pc st))
                                  (successors instr)).
Proof.
  intros until instr; intros PICK CODEAT [GOOD1 GOOD2].
  generalize (NS.pick_some _ _ _ PICK); intro PICK2.
  set (out := transf pc (abstr_value pc st)).
  generalize (propagate_succ_list_charact out (successors instr) {| aval := aval st; worklist := rem; visited := visited st |}).
  set (st' := propagate_succ_list {| aval := aval st; worklist := rem; visited := visited st |} out
                                  (successors instr)).
  simpl; intros (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9).
  constructor; intros.
- (* stable *)
  destruct (A8 n H); auto. destruct (A4 n); auto.
  replace (abstr_value n st') with (abstr_value n st)
  by (unfold abstr_value; rewrite H1; auto).
  exploit GOOD1; eauto. intros [P|P].
+ (* n was on the worklist *)
  rewrite PICK2 in P; destruct P.
  * (* node n is our node pc *)
    subst n. fold out. right; intros.
    assert (i = instr) by congruence. subst i.
    apply A1; auto.
  * (* n was already on the worklist *)
    left. apply A5; auto.
+ (* n was stable before, still is *)
  right; intros. apply optge_trans with st.(aval)!s; eauto.
- (* defined *)
  destruct st.(aval)!n as [v'|] eqn:ST.
  + apply A7. eapply GOOD2; eauto.
  + apply A9; auto. congruence.
Qed.

Lemma step_state_good_2:
  forall st pc rem,
  good_state st ->
  NS.pick (worklist st) = Some (pc, rem) ->
  code!pc = None ->
  good_state (mkstate st.(aval) rem st.(visited)).
Proof.
  intros until rem; intros [GOOD1 GOOD2] PICK CODE.
  generalize (NS.pick_some _ _ _ PICK); intro PICK2.
  constructor; simpl; intros.
- (* stable *)
  exploit GOOD1; eauto. intros [P | P].
  + rewrite PICK2 in P. destruct P; auto.
    subst n. right; intros. congruence.
  + right; exact P.
- (* defined *)
  eapply GOOD2; eauto.
Qed.

(* Lemma steps_incr: 
  forall n s1 s2, steps s1 s2 ->
  optge s2.(aval)!n s1.(aval)!n /\ (s1.(visited) n -> s2.(visited) n).
Proof.
  induction 1.
- split. apply optge_refl. auto.
- destruct IHsteps. exploit (step_incr n); eauto. intros [P Q].
  split. eapply optge_trans; eauto. eauto.
Qed. 
Record good_state (st: state) : Prop := {
  gs_stable: forall n,
    st.(visited) n -> 
    NS.In n st.(worklist) \/ 
    (forall i s, 
     code!n = Some i -> In s (successors i) ->
     optge st.(aval)!s (Some (transf n (abstr_value n st))));
  gs_defined: forall n v,
    st.(aval)!n = Some v -> st.(visited) n
}.
*)

(** 知道step_state_good, steps也就知道了 *)
Lemma steps_state_good:
  forall st1 st2, steps st1 st2 -> good_state st1 -> good_state st2.
Proof.
  induction 1; intros.
- auto.
- unfold step in e.
  destruct (NS.pick (worklist s2)) as [[n rem] | ] eqn:PICK; try discriminate.
  destruct (code!n) as [instr|] eqn:CODE; inv e.
  eapply step_state_good; eauto.
  eapply step_state_good_2; eauto.
Qed.

(** We show that initial states satisfy the invariant. *)
(** 说明起始状态满足good step*)
Lemma start_state_good:
  forall enode eval, good_state (start_state enode eval).
Proof.
  intros. unfold start_state; constructor; simpl; intros.
- subst n. rewrite NS.add_spec; auto.
- rewrite PTree.gsspec in H. rewrite PTree.gempty in H.
  destruct (peq n enode). auto. discriminate.
Qed.

Lemma start_state_nodeset_good:
  forall enodes, good_state (start_state_nodeset enodes).
Proof.
  intros. unfold start_state_nodeset; constructor; simpl; intros.
- left. auto.
- rewrite PTree.gempty in H. congruence.
Qed.

Lemma start_state_allnodes_good:
  good_state start_state_allnodes.
Proof.
  unfold start_state_allnodes; constructor; simpl; intros.
- destruct H as [instr CODE]. left. eapply NS.all_nodes_spec; eauto.
- rewrite PTree.gempty in H. congruence.
Qed.

(** Reachability in final states. *)
(** 这个应该是配合fixpoint_charact使用的 *)
Lemma reachable_visited:
  forall st, good_state st -> NS.pick st.(worklist) = None ->
  (** 对于每一个worklist为空的goodstate *)
  forall p q, reachable code successors p q -> st.(visited) p -> st.(visited) q.
  (** 如果p can reach q；那么如果p会被访问到，q一定会被访问到 *)
Proof.
  intros st [GOOD1 GOOD2] PICK. induction 1; intros.
- auto.
- eapply IHreachable; eauto.
  exploit GOOD1; eauto. intros [P | P].
  eelim NS.pick_none; eauto.
  exploit P; eauto. intros OGE; inv OGE. eapply GOOD2; eauto.
Qed.

(** ** Correctness of the solution returned by [fixpoint]. *)

(** As a consequence of the [good_state] invariant, the result of
  [fixpoint], if defined, is a solution of the dataflow inequations.
  This assumes that the transfer function maps [L.bot] to [L.bot]. *)
(** 此时，根据前面每个算法子结构性质的证明，可以说明完整算法的性质了 *)
(** goodstate中worklist entry的含义 => 结果worklist为空 => 结果满足fixpoint inequation *)
Theorem fixpoint_solution:
  forall ep ev res n instr s,
  fixpoint ep ev = Some res ->
  (** 算法最后的结果res *)
  code!n = Some instr ->
  In s (successors instr) ->
  (** 关于每一个结点n和它的后继s *)
  (forall n, L.eq (transf n L.bot) L.bot) ->  (** 这一条其实不太理解 *)
  L.ge res!!s (transf n res!!n).
  (** 都有inequation关系 *)
Proof.
  unfold fixpoint; intros.
  exploit fixpoint_from_charact; eauto. intros (st & STEPS & PICK & RES).
  exploit steps_state_good; eauto. apply start_state_good.  intros [GOOD1 GOOD2]. (** 把所有已知条件、定理应用，展开 *)
  (** 只需要证inequation: L.ge res !! s (transf n res !! n) *)
  rewrite RES; unfold PMap.get; simpl.  (** res表示转换，PMap -> PTree *)
  destruct st.(aval)!n as [v|] eqn:STN.  (** 对n点分析结果直接分类讨论，（其实应该一定存在这一点的结果的？），如果该点结果存在，直接拿出来，如果不存在，用L.bot作为默认；讨论两个分支 *)
- (** n有分析结果v *)
  destruct (GOOD1 n) as [P|P]. eauto.  (** case analysis on (GOOD1 n) *)
  { (** 如果结点n在worklist中 *)
    (** 应该是想说明终止了的程序，worklist一定为空？然后关闭这个分支？TODO *) 
    eelim NS.pick_none; eauto. 
  }
  {
    (** 结点n不在worklist中，根据goodstate定义，直接就过了 *)
    exploit P; eauto. unfold abstr_value; rewrite STN. intros OGE. inv OGE. auto.
  }
- (** n没有分析结果，qe成立也是显然的 *)
  apply L.ge_trans with L.bot. apply L.ge_bot. apply L.ge_refl. apply L.eq_sym. eauto.
Qed.

(** Moreover, the result of [fixpoint], if defined, satisfies the additional
  constraint given on the entry point. *)

Theorem fixpoint_entry:
  forall ep ev res,
  fixpoint ep ev = Some res ->
  L.ge res!!ep ev.
Proof.
  unfold fixpoint; intros.
  exploit fixpoint_from_charact; eauto. intros (st & STEPS & PICK & RES).
  exploit (steps_incr ep); eauto. simpl. rewrite PTree.gss. intros [P Q].
  rewrite RES; unfold PMap.get; simpl. inv P; auto.
Qed.

(** For [fixpoint_allnodes], we show that the result is a solution
  without assuming [transf n L.bot = L.bot]. *)

Theorem fixpoint_allnodes_solution:
  forall res n instr s,
  fixpoint_allnodes = Some res ->
  code!n = Some instr ->
  In s (successors instr) ->
  L.ge res!!s (transf n res!!n).
Proof.
  unfold fixpoint_allnodes; intros.
  exploit fixpoint_from_charact; eauto. intros (st & STEPS & PICK & RES).
  exploit steps_state_good; eauto. apply start_state_allnodes_good. intros [GOOD1 GOOD2].
  exploit (steps_incr n); eauto. simpl. intros [U V].
  exploit (GOOD1 n). apply V. exists instr; auto. intros [P|P].
  eelim NS.pick_none; eauto.
  exploit P; eauto. intros OGE. rewrite RES; unfold PMap.get; simpl.
  inv OGE. assumption.
Qed.

(** For [fixpoint_nodeset], we show that the result is a solution
  at all program points that are reachable from the given entry points. *)

Theorem fixpoint_nodeset_solution:
  forall enodes res e n instr s,
  fixpoint_nodeset enodes = Some res ->
  NS.In e enodes ->
  reachable code successors e n ->
  code!n = Some instr ->
  In s (successors instr) ->
  L.ge res!!s (transf n res!!n).
Proof.
  unfold fixpoint_nodeset; intros.
  exploit fixpoint_from_charact; eauto. intros (st & STEPS & PICK & RES).
  exploit steps_state_good; eauto. apply start_state_nodeset_good. intros GOOD.
  exploit (steps_incr e); eauto. simpl. intros [U V].
  assert (st.(visited) n).
  { eapply reachable_visited; eauto. }
  destruct GOOD as [GOOD1 GOOD2].
  exploit (GOOD1 n); eauto. intros [P|P].
  eelim NS.pick_none; eauto.
  exploit P; eauto. intros OGE. rewrite RES; unfold PMap.get; simpl.
  inv OGE. assumption.
Qed.

Check step.
(** ** Preservation of a property over solutions *)
(** 这个还得再理解下... TODO *)
Theorem fixpoint_invariant:
  forall ep ev
    (P: L.t -> Prop)
    (P_bot: P L.bot)
    (P_lub: forall x y, P x -> P y -> P (L.lub x y))
    (P_transf: forall pc instr x, code!pc = Some instr -> P x -> P (transf pc x))
    (P_entrypoint: P ev)
    res pc,
  fixpoint ep ev = Some res ->
  P res!!pc.
Proof.
  intros.
  set (inv := fun st => forall x, P (abstr_value x st)).
  assert (inv (start_state ep ev)).
  {
    red; simpl; intros. unfold abstr_value, start_state; simpl.
    rewrite PTree.gsspec. rewrite PTree.gempty.
    destruct (peq x ep). auto. auto.
  }
  assert (forall st v n, inv st -> P v -> inv (propagate_succ st v n)).
  {
    unfold inv, propagate_succ. intros.
    destruct (aval st)!n as [oldl|] eqn:E.
    destruct (L.beq oldl (L.lub oldl v)).
    auto.
    unfold abstr_value. simpl. rewrite PTree.gsspec. destruct (peq x n).
    apply P_lub; auto. replace oldl with (abstr_value n st). auto.
    unfold abstr_value; rewrite E; auto.
    apply H1.
    unfold abstr_value. simpl. rewrite PTree.gsspec. destruct (peq x n).
    auto.
    apply H1.
  }
  assert (forall l st v, inv st -> P v -> inv (propagate_succ_list st v l)).
  {
    induction l; intros; simpl. auto.
    apply IHl; auto.
  }
  assert (forall st1 st2, steps st1 st2 -> inv st1 -> inv st2).
  {
    induction 1; intros.
    auto.
    unfold step in e. destruct (NS.pick (worklist s2)) as [[n rem]|]; try discriminate.
    destruct (code!n) as [instr|] eqn:INSTR; inv e.
    apply H2. apply IHsteps; auto. eapply P_transf; eauto. apply IHsteps; auto.
    apply IHsteps; auto.
  }
  unfold fixpoint in H. exploit fixpoint_from_charact; eauto.
  intros (st & STEPS & PICK & RES).
  replace (res!!pc) with (abstr_value pc st). eapply H3; eauto.
  rewrite RES; auto.
Qed.

End Kildall.

End Dataflow_Solver.

(** * Solving backward dataflow problems using Kildall's algorithm *)

(** A backward dataflow problem on a given flow graph is a forward
  dataflow program on the reversed flow graph, where predecessors replace
  successors.  We exploit this observation to cheaply derive a backward
  solver from the forward solver. *)

(** ** Construction of the reversed flow graph (the predecessor relation) *)

Definition successors_list (successors: PTree.t (list positive)) (pc: positive) : list positive :=
  match successors!pc with None => nil | Some l => l end.

Notation "a !!! b" := (successors_list a b) (at level 1).

Section Predecessor.

Context {A: Type}.
Variable code: PTree.t A.
Variable successors: A -> list positive.

Fixpoint add_successors (pred: PTree.t (list positive))
                        (from: positive) (tolist: list positive)
                        {struct tolist} : PTree.t (list positive) :=
  match tolist with
  | nil => pred
  | to :: rem => add_successors (PTree.set to (from :: pred!!!to) pred) from rem
  end.

Lemma add_successors_correct:
  forall tolist from pred n s,
  In n pred!!!s \/ (n = from /\ In s tolist) ->
  In n (add_successors pred from tolist)!!!s.
Proof.
  induction tolist; simpl; intros.
  tauto.
  apply IHtolist.
  unfold successors_list at 1. rewrite PTree.gsspec. destruct (peq s a).
  subst a. destruct H. auto with coqlib.
  destruct H. subst n. auto with coqlib.
  fold (successors_list pred s). intuition congruence.
Qed.

Definition make_predecessors : PTree.t (list positive) :=
  PTree.fold (fun pred pc instr => add_successors pred pc (successors instr))
             code (PTree.empty (list positive)).

Lemma make_predecessors_correct_1:
  forall n instr s,
  code!n = Some instr -> In s (successors instr) ->
  In n make_predecessors!!!s.
Proof.
  intros until s.
  set (P := fun m p => m!n = Some instr -> In s (successors instr) ->
                       In n p!!!s).
  unfold make_predecessors.
  apply PTree_Properties.fold_rec with (P := P); unfold P; intros.
(* extensionality *)
  apply H0; auto. rewrite H; auto.
(* base case *)
  rewrite PTree.gempty in H; congruence.
(* inductive case *)
  apply add_successors_correct.
  rewrite PTree.gsspec in H2. destruct (peq n k).
  inv H2. auto.
  auto.
Qed.

Lemma make_predecessors_correct_2:
  forall n instr s,
  code!n = Some instr -> In s (successors instr) ->
  exists l, make_predecessors!s = Some l /\ In n l.
Proof.
  intros. exploit make_predecessors_correct_1; eauto.
  unfold successors_list. destruct (make_predecessors!s); simpl; intros.
  exists l; auto.
  contradiction.
Qed.

Lemma reachable_predecessors:
  forall p q,
  reachable code successors p q ->
  reachable make_predecessors (fun l => l) q p.
Proof.
  induction 1.
- constructor.
- exploit make_predecessors_correct_2; eauto. intros [l [P Q]].
  eapply reachable_right; eauto.
Qed.

End Predecessor.

(** ** Solving backward dataflow problems *)

(** The interface to a backward dataflow solver is as follows. *)

Module Type BACKWARD_DATAFLOW_SOLVER.

  Declare Module L: SEMILATTICE.

  (** [fixpoint successors transf] is the solver.
    It returns either an error or a mapping from program points to
    values of type [L.t] representing the solution.  [successors]
    is a finite map returning the list of successors of the given program
    point. [transf] is the transfer function. *)

  Parameter fixpoint:
    forall {A: Type} (code: PTree.t A) (successors: A -> list positive)
           (transf: positive -> L.t -> L.t),
    option (PMap.t L.t).

  (** The [fixpoint_solution] theorem shows that the returned solution,
    if any, satisfies the backward dataflow inequations. *)

  Axiom fixpoint_solution:
    forall A (code: PTree.t A) successors transf res n instr s,
    fixpoint code successors transf = Some res ->
    code!n = Some instr -> In s (successors instr) ->
    (forall n a, code!n = None -> L.eq (transf n a) L.bot) ->
    L.ge res!!n (transf s res!!s).

  (** [fixpoint_allnodes] is a variant of [fixpoint], less algorithmically
    efficient, but correct without any hypothesis on the transfer function. *)

  Parameter fixpoint_allnodes:
    forall {A: Type} (code: PTree.t A) (successors: A -> list positive)
           (transf: positive -> L.t -> L.t),
    option (PMap.t L.t).

  Axiom fixpoint_allnodes_solution:
    forall A (code: PTree.t A) successors transf res n instr s,
    fixpoint_allnodes code successors transf = Some res ->
    code!n = Some instr -> In s (successors instr) ->
    L.ge res!!n (transf s res!!s).

End BACKWARD_DATAFLOW_SOLVER.

(** We construct a generic backward dataflow solver, working over any
  semi-lattice structure, by applying the forward dataflow solver
  with the predecessor relation instead of the successor relation. *)

Module Backward_Dataflow_Solver (LAT: SEMILATTICE) (NS: NODE_SET):
                   BACKWARD_DATAFLOW_SOLVER with Module L := LAT.

Module L := LAT.

Module DS := Dataflow_Solver L NS.

Section Kildall.

Context {A: Type}.
Variable code: PTree.t A.
Variable successors: A -> list positive.
Variable transf: positive -> L.t -> L.t.

(** Finding entry points for the reverse control-flow graph. *)

Section Exit_points.

(** Assuming that the nodes of the CFG [code] are numbered in reverse
  postorder (cf. pass [Renumber]), an edge from [n] to [s] is a
  normal edge if [s < n] and a back-edge otherwise.
  [sequential_node] returns [true] if the given node has at least one
  normal outgoing edge.  It returns [false] if the given node is an exit
  node (no outgoing edges) or the final node of a loop body
  (all outgoing edges are back-edges).  As we prove later, the set
  of all non-sequential node is an appropriate set of entry points
  for exploring the reverse CFG. *)

Definition sequential_node (pc: positive) (instr: A): bool :=
  existsb (fun s => match code!s with None => false | Some _ => plt s pc end)
          (successors instr).

Definition exit_points : NS.t :=
  PTree.fold
    (fun ep pc instr =>
       if sequential_node pc instr
       then ep
       else NS.add pc ep)
    code NS.empty.

Lemma exit_points_charact:
  forall n,
  NS.In n exit_points <-> exists i, code!n = Some i /\ sequential_node n i = false.
Proof.
  intros n. unfold exit_points. eapply PTree_Properties.fold_rec.
- (* extensionality *)
  intros. rewrite <- H. auto.
- (* base case *)
  simpl. split; intros.
  eelim NS.empty_spec; eauto.
  destruct H as [i [P Q]]. rewrite PTree.gempty in P. congruence.
- (* inductive case *)
  intros. destruct (sequential_node k v) eqn:SN.
  + rewrite H1. rewrite PTree.gsspec. destruct (peq n k).
    subst. split; intros [i [P Q]]. congruence. inv P. congruence.
    tauto.
  + rewrite NS.add_spec. rewrite H1. rewrite PTree.gsspec. destruct (peq n k).
    subst. split. intros. exists v; auto. auto.
    split. intros [P | [i [P Q]]]. congruence. exists i; auto.
    intros [i [P Q]]. right; exists i; auto.
Qed.

Lemma reachable_exit_points:
  forall pc i,
  code!pc = Some i -> exists x, NS.In x exit_points /\ reachable code successors pc x.
Proof.
  intros pc0. pattern pc0. apply (well_founded_ind Plt_wf).
  intros pc HR i CODE.
  destruct (sequential_node pc i) eqn:SN.
- (* at least one successor that decreases the pc *)
  unfold sequential_node in SN. rewrite existsb_exists in SN.
  destruct SN as [s [P Q]]. destruct (code!s) as [i'|] eqn:CS; try discriminate. InvBooleans.
  exploit (HR s); eauto. intros [x [U V]].
  exists x; split; auto. eapply reachable_left; eauto.
- (* otherwise we are an exit point *)
  exists pc; split.
  rewrite exit_points_charact. exists i; auto. constructor.
Qed.

(** The crucial property of exit points is that any nonempty node in the
  CFG is reverse-reachable from an exit point. *)

Lemma reachable_exit_points_predecessor:
  forall pc i,
  code!pc = Some i ->
  exists x, NS.In x exit_points /\ reachable (make_predecessors code successors) (fun l => l) x pc.
Proof.
  intros. exploit reachable_exit_points; eauto. intros [x [P Q]].
  exists x; split; auto. apply reachable_predecessors. auto.
Qed.

End Exit_points.

(** The efficient backward solver.  *)

Definition fixpoint :=
  DS.fixpoint_nodeset
    (make_predecessors code successors) (fun l => l)
    transf exit_points.

Theorem fixpoint_solution:
  forall res n instr s,
  fixpoint = Some res ->
  code!n = Some instr -> In s (successors instr) ->
  (forall n a, code!n = None -> L.eq (transf n a) L.bot) ->
  L.ge res!!n (transf s res!!s).
Proof.
  intros.
  exploit (make_predecessors_correct_2 code); eauto. intros [l [P Q]].
  destruct code!s as [instr'|] eqn:CS.
- exploit reachable_exit_points_predecessor. eexact CS. intros (ep & U & V).
  unfold fixpoint in H. eapply DS.fixpoint_nodeset_solution; eauto.
- apply L.ge_trans with L.bot. apply L.ge_bot.
  apply L.ge_refl. apply L.eq_sym. auto.
Qed.

(** The alternate solver that starts with all nodes of the CFG instead
  of just the exit points. *)

Definition fixpoint_allnodes :=
  DS.fixpoint_allnodes
    (make_predecessors code successors) (fun l => l)
    transf.

Theorem fixpoint_allnodes_solution:
  forall res n instr s,
  fixpoint_allnodes = Some res ->
  code!n = Some instr -> In s (successors instr) ->
  L.ge res!!n (transf s res!!s).
Proof.
  intros.
  exploit (make_predecessors_correct_2 code); eauto. intros [l [P Q]].
  unfold fixpoint_allnodes in H.
  eapply DS.fixpoint_allnodes_solution; eauto.
Qed.

End Kildall.

End Backward_Dataflow_Solver.

(** * Analysis on extended basic blocks *)

(** We now define an approximate solver for forward dataflow problems
  that proceeds by forward propagation over extended basic blocks.
  In other terms, program points with multiple predecessors are mapped
  to [L.top] (the greatest, or coarsest, approximation) and the other
  program points are mapped to [transf p X[p]] where [p] is their unique
  predecessor.

  This analysis applies to any type of approximations equipped with
  an ordering and a greatest element. *)

Module Type ORDERED_TYPE_WITH_TOP.

  Parameter t: Type.
  Parameter ge: t -> t -> Prop.
  Parameter top: t.
  Axiom top_ge: forall x, ge top x.
  Axiom refl_ge: forall x, ge x x.

End ORDERED_TYPE_WITH_TOP.

(** The interface of the solver is similar to that of Kildall's forward
  solver, with a slightly different statement of the invariant
  preservation property [fixpoint_invariant]. *)

Module Type BBLOCK_SOLVER.

  Declare Module L: ORDERED_TYPE_WITH_TOP.

  Parameter fixpoint:
    forall {A: Type} (code: PTree.t A) (successors: A -> list positive)
           (transf: positive -> L.t -> L.t)
           (entrypoint: positive),
    option (PMap.t L.t).

  Axiom fixpoint_solution:
    forall A (code: PTree.t A) successors transf entrypoint res n instr s,
    fixpoint code successors transf entrypoint = Some res ->
    code!n = Some instr -> In s (successors instr) ->
    L.ge res!!s (transf n res!!n).

  Axiom fixpoint_entry:
    forall A (code: PTree.t A) successors transf entrypoint res,
    fixpoint code successors transf entrypoint = Some res ->
    res!!entrypoint = L.top.

  Axiom fixpoint_invariant:
    forall A (code: PTree.t A) successors transf entrypoint
           (P: L.t -> Prop),
    P L.top ->
    (forall pc instr x, code!pc = Some instr -> P x -> P (transf pc x)) ->
    forall res pc,
    fixpoint code successors transf entrypoint = Some res ->
    P res!!pc.

End BBLOCK_SOLVER.

(** The implementation of the ``extended basic block'' solver is a
  functor parameterized by any ordered type with a top element. *)

Module BBlock_solver(LAT: ORDERED_TYPE_WITH_TOP):
                        BBLOCK_SOLVER with Module L := LAT.

Module L := LAT.

Section Solver.

Context {A: Type}.
Variable code: PTree.t A.
Variable successors: A -> list positive.
Variable transf: positive -> L.t -> L.t.
Variable entrypoint: positive.
Variable P: L.t -> Prop.
Hypothesis Ptop: P L.top.
Hypothesis Ptransf: forall pc instr x, code!pc = Some instr -> P x -> P (transf pc x).

Definition bbmap := positive -> bool.
Definition result := PMap.t L.t.

(** As in Kildall's solver, the state of the iteration has two components:
- A mapping from program points to values of type [L.t] representing
  the candidate solution found so far.
- A worklist of program points that remain to be considered.
*)

Record state : Type := mkstate
  { aval: result; worklist: list positive }.

(** The ``extended basic block'' algorithm, in pseudo-code, is as follows:
<<
    worklist := the set of all points n having multiple predecessors
    aval  := the mapping n -> L.top

    while worklist is not empty, do
        extract a node n from worklist
        compute out = transf n aval[n]
        for each successor s of n:
            if s has only one predecessor (namely, n):
                aval[s] := out
                worklist := worklist union {s}
            end if
        end for
    end while
    return aval
>>
**)

Fixpoint propagate_successors
    (bb: bbmap) (succs: list positive) (l: L.t) (st: state)
    {struct succs} : state :=
  match succs with
  | nil => st
  | s1 :: sl =>
      if bb s1 then
        propagate_successors bb sl l st
      else
        propagate_successors bb sl l
          (mkstate (PMap.set s1 l st.(aval))
                   (s1 :: st.(worklist)))
  end.

Definition step (bb: bbmap) (st: state) : result + state :=
  match st.(worklist) with
  | nil => inl _ st.(aval)
  | pc :: rem =>
      match code!pc with
      | None =>
          inr _ (mkstate st.(aval) rem)
      | Some instr =>
          inr _ (propagate_successors
                   bb (successors instr)
                   (transf pc st.(aval)!!pc)
                   (mkstate st.(aval) rem))
      end
  end.

(** Recognition of program points that have more than one predecessor. *)

Definition is_basic_block_head
    (preds: PTree.t (list positive)) (pc: positive) : bool :=
  if peq pc entrypoint then true else
    match preds!!!pc with
    | nil => false
    | s :: nil => peq s pc
    | _ :: _ :: _ => true
    end.

Definition basic_block_map : bbmap :=
  is_basic_block_head (make_predecessors code successors).

Definition basic_block_list (bb: bbmap) : list positive :=
  PTree.fold (fun l pc instr => if bb pc then pc :: l else l)
             code nil.

(** The computation of the approximate solution. *)

Definition fixpoint : option result :=
  let bb := basic_block_map in
  PrimIter.iterate _ _ (step bb) (mkstate (PMap.init L.top) (basic_block_list bb)).

(** ** Properties of predecessors and multiple-predecessors nodes *)

Definition predecessors := make_predecessors code successors.

Lemma predecessors_correct:
  forall n instr s,
  code!n = Some instr -> In s (successors instr) -> In n predecessors!!!s.
Proof.
  intros. unfold predecessors. eapply make_predecessors_correct_1; eauto.
Qed.

Lemma multiple_predecessors:
  forall s n1 instr1 n2 instr2,
  code!n1 = Some instr1 -> In s (successors instr1) ->
  code!n2 = Some instr2 -> In s (successors instr2) ->
  n1 <> n2 ->
  basic_block_map s = true.
Proof.
  intros.
  assert (In n1 predecessors!!!s). eapply predecessors_correct; eauto.
  assert (In n2 predecessors!!!s). eapply predecessors_correct; eauto.
  unfold basic_block_map, is_basic_block_head.
  destruct (peq s entrypoint). auto.
  fold predecessors.
  destruct (predecessors!!!s).
  auto.
  destruct l.
  apply proj_sumbool_is_true. simpl in *. intuition congruence.
  auto.
Qed.

Lemma no_self_loop:
  forall n instr,
  code!n = Some instr -> In n (successors instr) -> basic_block_map n = true.
Proof.
  intros. unfold basic_block_map, is_basic_block_head.
  destruct (peq n entrypoint). auto.
  fold predecessors.
  exploit predecessors_correct; eauto. intros.
  destruct (predecessors!!!n).
  contradiction.
  destruct l. apply proj_sumbool_is_true. simpl in H1. tauto.
  auto.
Qed.

(** ** Correctness invariant *)

(** The invariant over the state is as follows:
- Points with several predecessors are mapped to [L.top]
- Points not in the worklist satisfy their inequations
  (as in Kildall's algorithm).
*)

Definition state_invariant (st: state) : Prop :=
  (forall n, basic_block_map n = true -> st.(aval)!!n = L.top)
/\
  (forall n,
   In n st.(worklist) \/
   (forall instr s, code!n = Some instr -> In s (successors instr) ->
               L.ge st.(aval)!!s (transf n st.(aval)!!n))).

Lemma propagate_successors_charact1:
  forall bb succs l st,
  incl st.(worklist)
       (propagate_successors bb succs l st).(worklist).
Proof.
  induction succs; simpl; intros.
  apply incl_refl.
  case (bb a).
  auto.
  apply incl_tran with (a :: worklist st).
  apply incl_tl. apply incl_refl.
  set (st1 := (mkstate (PMap.set a l (aval st)) (a :: worklist st))).
  change (a :: worklist st) with (worklist st1).
  auto.
Qed.

Lemma propagate_successors_charact2:
  forall bb succs l st n,
  let st' := propagate_successors bb succs l st in
  (In n succs -> bb n = false -> In n st'.(worklist) /\ st'.(aval)!!n = l)
/\ (~In n succs \/ bb n = true -> st'.(aval)!!n = st.(aval)!!n).
Proof.
  induction succs; simpl; intros.
  (* Base case *)
  split. tauto. auto.
  (* Inductive case *)
  caseEq (bb a); intro.
  elim (IHsuccs l st n); intros U V.
  split; intros. apply U; auto.
  elim H0; intro. subst a. congruence. auto.
  apply V. tauto.
  set (st1 := mkstate (PMap.set a l (aval st)) (a :: worklist st)).
  elim (IHsuccs l st1 n); intros U V.
  split; intros.
  elim H0; intros.
  subst n. split.
  apply propagate_successors_charact1. simpl. tauto.
  case (In_dec peq a succs); intro.
  elim (U i H1); auto.
  rewrite V. unfold st1; simpl. apply PMap.gss. tauto.
  apply U; auto.
  rewrite V. unfold st1; simpl. apply PMap.gso.
  red; intro; subst n. elim H0; intro. tauto. congruence.
  tauto.
Qed.

Lemma propagate_successors_invariant:
  forall pc instr res rem,
  code!pc = Some instr ->
  state_invariant (mkstate res (pc :: rem)) ->
  state_invariant
    (propagate_successors basic_block_map (successors instr)
                          (transf pc res!!pc)
                          (mkstate res rem)).
Proof.
  intros until rem. intros CODE [INV1 INV2]. simpl in INV1. simpl in INV2.
  set (l := transf pc res!!pc).
  generalize (propagate_successors_charact1 basic_block_map
                (successors instr) l (mkstate res rem)).
  generalize (propagate_successors_charact2 basic_block_map
                (successors instr) l (mkstate res rem)).
  set (st1 := propagate_successors basic_block_map
                 (successors instr) l (mkstate res rem)).
  intros U V. simpl in U.
  (* First part: BB entries remain at top *)
  split; intros.
  elim (U n); intros C D. rewrite D. simpl. apply INV1. auto. tauto.
  (* Second part: monotonicity *)
  (* Case 1: n = pc *)
  destruct (peq pc n). subst n.
  right; intros.
  assert (instr0 = instr) by congruence. subst instr0.
  elim (U s); intros C D.
  replace (st1.(aval)!!pc) with res!!pc. fold l.
  destruct (basic_block_map s) eqn:BB.
  rewrite D. simpl. rewrite INV1. apply L.top_ge. auto. tauto.
  elim (C H0 (eq_refl _)). intros X Y. rewrite Y. apply L.refl_ge.
  elim (U pc); intros E F. rewrite F. reflexivity.
  destruct (In_dec peq pc (successors instr)).
  right. eapply no_self_loop; eauto.
  left; auto.
  (* Case 2: n <> pc *)
  elim (INV2 n); intro.
  (* Case 2.1: n was already in worklist, still is *)
  left. apply V. simpl. tauto.
  (* Case 2.2: n was not in worklist *)
  assert (INV3: forall s instr', code!n = Some instr' -> In s (successors instr') -> st1.(aval)!!s = res!!s).
    (* Amazingly, successors of n do not change.  The only way
       they could change is if they were successors of pc as well,
       but that gives them two different predecessors, so
       they are basic block heads, and thus do not change! *)
    intros. elim (U s); intros C D. rewrite D. reflexivity.
    destruct (In_dec peq s (successors instr)).
    right. eapply multiple_predecessors with (n1 := pc) (n2 := n); eauto.
    left; auto.
  destruct (In_dec peq n (successors instr)).
  (* Case 2.2.1: n is a successor of pc. Either it is in the
     worklist or it did not change *)
  destruct (basic_block_map n) eqn:BB.
  right; intros.
  elim (U n); intros C D. rewrite D. erewrite INV3; eauto.
  tauto.
  left. elim (U n); intros C D. elim (C i BB); intros. auto.
  (* Case 2.2.2: n is not a successor of pc. It did not change. *)
  right; intros.
  elim (U n); intros C D. rewrite D.
  erewrite INV3; eauto.
  tauto.
Qed.

Lemma propagate_successors_invariant_2:
  forall pc res rem,
  code!pc = None ->
  state_invariant (mkstate res (pc :: rem)) ->
  state_invariant (mkstate res rem).
Proof.
  intros until rem. intros CODE [INV1 INV2]. simpl in INV1. simpl in INV2.
  split; simpl; intros.
  apply INV1; auto.
  destruct (INV2 n) as [[U | U] | U].
  subst n. right; intros; congruence.
  auto.
  auto.
Qed.

Lemma initial_state_invariant:
  state_invariant (mkstate (PMap.init L.top) (basic_block_list basic_block_map)).
Proof.
  split; simpl; intros.
  apply PMap.gi.
  right. intros. repeat rewrite PMap.gi. apply L.top_ge.
Qed.

Lemma analyze_invariant:
  forall res,
  fixpoint = Some res ->
  state_invariant (mkstate res nil).
Proof.
  unfold fixpoint; intros. pattern res.
  eapply (PrimIter.iterate_prop _ _ (step basic_block_map)
           state_invariant).

  intros st INV. destruct st as [stin stwrk].
  unfold step. simpl. destruct stwrk as [ | pc rem ] eqn:WRK.
  auto.
  destruct (code!pc) as [instr|] eqn:CODE.
  eapply propagate_successors_invariant; eauto.
  eapply propagate_successors_invariant_2; eauto.

  eauto. apply initial_state_invariant.
Qed.

(** ** Correctness of the returned solution *)

Theorem fixpoint_solution:
  forall res n instr s,
  fixpoint = Some res ->
  code!n = Some instr -> In s (successors instr) ->
  L.ge res!!s (transf n res!!n).
Proof.
  intros.
  assert (state_invariant (mkstate res nil)).
  eapply analyze_invariant; eauto.
  elim H2; simpl; intros.
  elim (H4 n); intros.
  contradiction.
  eauto.
Qed.

Theorem fixpoint_entry:
  forall res,
  fixpoint = Some res ->
  res!!entrypoint = L.top.
Proof.
  intros.
  assert (state_invariant (mkstate res nil)).
  eapply analyze_invariant; eauto.
  elim H0; simpl; intros.
  apply H1. unfold basic_block_map, is_basic_block_head.
  fold predecessors. apply peq_true.
Qed.

(** ** Preservation of a property over solutions *)

Definition Pstate (st: state) : Prop :=
  forall pc, P st.(aval)!!pc.

Lemma propagate_successors_P:
  forall bb l,
  P l ->
  forall succs st,
  Pstate st ->
  Pstate (propagate_successors bb succs l st).
Proof.
  induction succs; simpl; intros.
  auto.
  case (bb a). auto.
  apply IHsuccs. red; simpl; intros.
  rewrite PMap.gsspec. case (peq pc a); intro.
  auto. apply H0.
Qed.

Theorem fixpoint_invariant:
  forall res pc, fixpoint = Some res -> P res!!pc.
Proof.
  unfold fixpoint; intros. pattern res.
  eapply (PrimIter.iterate_prop _ _ (step basic_block_map) Pstate).

  intros st PS. unfold step. destruct (st.(worklist)).
  apply PS.
  assert (PS2: Pstate (mkstate st.(aval) l)).
    red; intro; simpl. apply PS.
  destruct (code!p) as [instr|] eqn:CODE.
  apply propagate_successors_P. eauto. auto.
  auto.

  eauto.
  red; intro; simpl. rewrite PMap.gi. apply Ptop.
Qed.

End Solver.

End BBlock_solver.

(** ** Node sets *)

(** We now define implementations of the [NODE_SET] interface
  appropriate for forward and backward dataflow analysis.
  As mentioned earlier, we aim for a traversal of the CFG nodes
  in reverse postorder (for forward analysis) or postorder
  (for backward analysis).  We take advantage of the following
  fact, valid for all CFG generated by translation from Cminor:
  the enumeration [n-1], [n-2], ..., 3, 2, 1 where [n] is the
  top CFG node is a reverse postorder traversal.
  Therefore, for forward analysis, we will use an implementation
  of [NODE_SET] where the [pick] operation selects the
  greatest node in the working list.  For backward analysis,
  we will similarly pick the smallest node in the working list. *)

Require Import Heaps.

Module NodeSetForward <: NODE_SET.
  Definition t := PHeap.t.
  Definition empty := PHeap.empty.
  Definition add (n: positive) (s: t) : t := PHeap.insert n s.
  Definition pick (s: t) :=
    match PHeap.findMax s with
    | Some n => Some(n, PHeap.deleteMax s)
    | None => None
    end.
  Definition all_nodes {A: Type} (code: PTree.t A) :=
    PTree.fold (fun s pc instr => PHeap.insert pc s) code PHeap.empty.
  Definition In := PHeap.In.

  Lemma empty_spec:
    forall n, ~In n empty.
  Proof.
    intros. apply PHeap.In_empty.
  Qed.

  Lemma add_spec:
    forall n n' s, In n' (add n s) <-> n = n' \/ In n' s.
  Proof.
    intros. rewrite PHeap.In_insert. unfold In. intuition.
  Qed.

  Lemma pick_none:
    forall s n, pick s = None -> ~In n s.
  Proof.
    intros until n; unfold pick. caseEq (PHeap.findMax s); intros.
    congruence.
    apply PHeap.findMax_empty. auto.
  Qed.

  Lemma pick_some:
    forall s n s', pick s = Some(n, s') ->
    forall n', In n' s <-> n = n' \/ In n' s'.
  Proof.
    intros until s'; unfold pick. caseEq (PHeap.findMax s); intros.
    inv H0.
    generalize (PHeap.In_deleteMax s n n' H). unfold In. intuition.
    congruence.
  Qed.

  Lemma all_nodes_spec:
    forall A (code: PTree.t A) n instr,
    code!n = Some instr -> In n (all_nodes code).
  Proof.
    intros A code n instr.
    apply PTree_Properties.fold_rec with
      (P := fun m set => m!n = Some instr -> In n set).
    (* extensionality *)
    intros. apply H0. rewrite H. auto.
    (* base case *)
    rewrite PTree.gempty. congruence.
    (* inductive case *)
    intros. rewrite PTree.gsspec in H2. rewrite add_spec.
    destruct (peq n k). auto. eauto.
  Qed.
End NodeSetForward.

Module NodeSetBackward <: NODE_SET.
  Definition t := PHeap.t.
  Definition empty := PHeap.empty.
  Definition add (n: positive) (s: t) : t := PHeap.insert n s.
  Definition pick (s: t) :=
    match PHeap.findMin s with
    | Some n => Some(n, PHeap.deleteMin s)
    | None => None
    end.
  Definition all_nodes {A: Type} (code: PTree.t A) :=
    PTree.fold (fun s pc instr => PHeap.insert pc s) code PHeap.empty.
  Definition In := PHeap.In.

  Lemma empty_spec:
    forall n, ~In n empty.
  Proof NodeSetForward.empty_spec.

  Lemma add_spec:
    forall n n' s, In n' (add n s) <-> n = n' \/ In n' s.
  Proof NodeSetForward.add_spec.

  Lemma pick_none:
    forall s n, pick s = None -> ~In n s.
  Proof.
    intros until n; unfold pick. caseEq (PHeap.findMin s); intros.
    congruence.
    apply PHeap.findMin_empty. auto.
  Qed.

  Lemma pick_some:
    forall s n s', pick s = Some(n, s') ->
    forall n', In n' s <-> n = n' \/ In n' s'.
  Proof.
    intros until s'; unfold pick. caseEq (PHeap.findMin s); intros.
    inv H0.
    generalize (PHeap.In_deleteMin s n n' H). unfold In. intuition.
    congruence.
  Qed.

  Lemma all_nodes_spec:
    forall A (code: PTree.t A) n instr,
    code!n = Some instr -> In n (all_nodes code).
  Proof NodeSetForward.all_nodes_spec.
End NodeSetBackward.
