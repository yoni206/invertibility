%Summary of "Provably correct peephole optimizations with alive"
Why
===
I read it, understood it, played with and inside the tool, and forgot everything.
Want it to not happen again.

Executive Summary
=================
- Alive is both a language and a tool.
- The language expresses optimizations. The tool verifies them.
- It even genreates c++ code for the optimization (unrelated to my project).
- InstCombine: a(n optimization?) pass in llvm that performs alerbraic simplifications.
	It is a file in llvm that contains optimizations. very buggy.
- Example of an InstCombine transformation: (x xor -1) + C => (C-1)-x, where x is a variable and C is a constant with the same width as x.
- In llvm, the code that represents this transformation is a c++ code. In alive it is a simple alive file, whose content is:
```
%1 = xor %x, -1
%2 = add %1, C
=>
%2 = sub C-1, %x
```

Alive Language
==============
In the paper.
Have the form `<precondition> <stmt> => <stmt>`, where `<precondition>` is optional.
The first `<stmt>` is called the *source template*. The second is called the *target template*.
The source and target templates must share a *root variable*
The representation is based on SSA.
TODO understand ssa and root variable.

Instruction Attributes
-----------------------
- In llvm there are three instruction attributes: `nsw`, `nuw` and `exact`.
TODO explain each one.

Types
-----
- Alive supports a subset of llvm's types. 
- Alive's types are: 
  - Integer types (I): i1, i2, ... with bitwidths 1,2,...
  - pointer types (P): `t*` is a type for every type t of alive.
  - array types (A): nxt for a natural number n and type t is a type.
  - void type
  - `FC` (first class types) - I and P. These are the only types that can be the result of an instruction.
  - does not support fp, records, vectors, etc.

Bitwidth independence
---------------------
- Integer variables in alive do not need an explicit bitwidth.
- Alive transformations are polymorphic w.r.t. all types that satify the constraints imposed by the instructions.
- These are the *feasible types*
- the verification is done for every possible type assignment, up to 64bit integers.
- for transformations without undefined values in the source template, we get QF_BV. sweet.

Undefined Behaviours
--------------------
- LLVM has 3 kinds of underfined behaviour.
- undefined behaviour - anything can happen.
- example: `sdiv a,b` is defined only when b!=0 and either a is not INT_MIN or b is not -1.
- Table 1 in the paper shows all operations whose definedness conditions are not `true`, except memoery instructions.
- in llvm ir there is `undef` value, which mimics a register that can return anything.
- `undef` stands for the set of all possible bit patterns for a particular type.
- The optimizer is allowed to pick any value for `undef`.

Poison Values
-------------
- distinct from `undef`. `undef` really occurs in a command in alive. `poison` is only implicit via the attributes.
- indicate that a side-effect-free instruction has a condition that produces undefined behaviour.
- they are not explicitly represented in the IR
TODO - is that still true?
- they are just values of operations that may have side effects that cause them to be undef.
- *poison free*: there are conditions that ensure that an operation will not produce a poison value.

Instruction Attributes
----------------------
- modify the behaviour of an instruction.
- nsw (no signed wrap): signed overflow is undefined
- nuw (no unsigned wrap): unsigned wrap undefined
- exact: used for shift right and divide
- For example, x+1>x can be rewritten to true if + is attributed with nsw and > is signed comparison. Why? If there is no overflow then ofcourse. Otherwise, x+1 is poison. This taints subsequent instructions, like > . And so the check itself is undefined, we can choose that it is true.
- x+1 is not only undefined. It is poison. Whatever depends on it is undefined!

Memory
------
TODO write details if needed later.

The Verification Process - no memory
=========================
VC Gen (verification condition generator) (sec 3.1.1)
------------------------------------------
- no biggie in the absence of undefined behaviour in the source and in the target. Just equivalence checking.
- In the presence of an undefined behaviour, equivalence checking is not enough.
- use refinement.
- The target of a transformation *refines* the source if every behaviour of the target is a behaviour of the source.
- undef: any `undef` in the source represents a set of possible values. The target can choose any one of them, but not outside of them.
- poison: verify that if the source did not yield a poison value, then the target will not yield a poison value, for every specific choice of input values.
- To summarize alive checks three things:
  - the target is defined whenever the source is defined.
  - the target is poson-free whenever the source is poison-free.
  - the source and the target produce the same result when the result is defined and poison free.


VC Gen (verification condition generator) (sec 3.1.2)
------------------------------------------
For each *instruction*, alive produces 3 smt expressions:
1. an expression for the result of the operation (except if the return type is void).
2. an expression representing the cases for which the instruction has defined behaviour.
3. an expression representing the cases for which an instruction does not return a poison value.

The VC Gen propagates definedness and poison-freenes so the definedness (poison-freenes) condition for an instruction is the conjunction of the condition of itself, and the conditions for all of its operands.

- undef: each undef is encoded as a fresh variable, that is added to a set U (I am assuming U is outside the smt formula).
- precondition predicates: depends on the semantics of llvm - some predicates are useable only if positive. In such a case, they are replace with a fresh boolean var `b`, and a one-direction condition is added b=>predicate. The effect is that if the predicate does not hold, be is unusable. On the other hand, some predicates are useful only in some cases. in such a case they are also replaced with a fresh boolean `b`, and a one-direction condition: s=>b, where b is the expression representing the cases. Something like that.

Actual formulas (sec 3.1.2)
----------------
- Let T be a transformation, phi be its precondition, A its source and B its target. 
We are not considering memory operations here, so every instruction in A and B has the form reg = ? for some reg. 
It is not explicitly explained how source instructions relate to target instructions. I think that there is at least the underlying assumption that there is one (root) register shared between source and target, and that .... i don't know. And in the example they chose a too simple example. NU SHOIN.
For every instruction i in T, let delta (delta') be the definedness constraint for the source (target) instruction, ro (ro') be the poison-free constraint of the source (target) instruction, and tau (tau') be the result of executing the source (target) instruction. `tau` is a term! not a formula! And again, it is not clear to me how to correspond source and target instructions to one another.
- Let I be the set of input variables in the source template, including constants, P the set of all fresh boolean variables (explained above), and U (U') the set of fresh variables that encode undef in the source (target).
-Let psi = phi/\delta/\ro.
- T is correct iff the following holds for every instruction i in T:
  - forall I,P,U' exists U . psi => delta'
  - forall I,P,U' exists U . psi => ro'
  - forall I,P,U' exists U . psi => tau=tau'

I think that the issue with the quantifiers is that the we actually want to prove congruence, not only equivalence, since the target may later appear as a source. 
For example, suppose we have an optimization `undef` => `undef`. We assign `u1` and `u2` to both. It is not enough to prove that there are `u1` and `u2` for which the above implications hold. We need that the first can always be replaced by the second. No matter what is u2, we must have some u1.
Perhaps the following example will help.

Example without `undef`
-----------------------

```
Pre: C1 u>= C2   (u>= is unsigned >=)
%0 = shl nsw i8 %a, C1
%1 = ashr %0, C2
  =>
%1 = shl nsw %a, C1-C2
```

- Definedness: when is the first source instruction defined? Exactly when shl is defined, which is when `C1 < width(C1)` holds. Somehow, it can be inferred that `width(C1)=8` (as this is the width of `%a`), and so this is equivalent to `C1 u< 8`. The second instruction is defined whenever `ashr` is defined, which is `C2 u< 8`, and its operands are defined. So. delta%0 = C2 u< 8 and delta%1 = C1 u< 8 /\ C2 u< 8. The target instruction is defined iff `delta'%1=(width C1-C2) u< 8`. For some reason, they also mention that `delta'%0=delta%0`. But I don't get it. There is no operation like that in the target. 
- Poison-freeness: The first source instruction is poison free if `(%a << C1) >> C1 = %a` holds. The second source instruction is poison free iff its operands are. So ro%1=ro%0=`(%a << C1) >> C1 = %a`. The target instruction is poison free iff `ro'%1=((%a << (C1 - C2) >> (C1 -C2) = %a)` holds. Similarly to above, `ro'%0=ro%0`.
- Values: tau'%0=tau%0 = %a << C1. tau%1 = (a << C2) >> C2. tau'%2 = a << (C1 - C2).
- undefined values: none.
- psi: phi /\ delta%1 /\ ro%1. We need to make sure that:
1. forall a, C1, C2 . psi => delta'%1
2. forall a, C1, C2 . psi => ro'%1
3. forall a, C1, C2 . psi => tau%1=tau'%1

We actually need to make sure that the same constraints hold for other formulas. But for %0, the source and target formulas are identical, and psi includes the source so it should be ok.

Example with `undef` 
----------------------
```
%r = select undef, i4 -1, 0
  =>
%r = ashr undef, 3
```

Strangely, both source and target are always defined! `delta%r=delta'%r=true`. This is because `select` is always defined, and `ashr`'s definedness condition depends only on the second argument.
Nevertheless, we do have `undef` occurrences.
We generate two fresh variables, `u1` and `u2` for the source and target `undef`s accordingly.
Both source and target are also poison free, because they don't have any attribute.
`ro%r=ro'%0=true`.
Now, `tau%r=ite(u1=1, -1, 0)` and `tau'%r=u2>>3`.
We need to check 3 conditions. But in two of them, the consequent is true so no need. The third:
`forall u2 exists u1 . tau=ite(u1=1,-1,0)=u2 >> 3`.
