# Lambda LF

> Implementation of a simple dependently typing language, based on *Advanced Topics in Types and Programming Languages*


## Kind Restriction

Notice that, the freedom given by this system is rather limited. For example, notice the K-PI rule.

$$\frac{\Gamma \vdash T_1 :: * \quad \Gamma, x : T_1 \vdash T_2 :: *}{\Gamma \vdash \Pi x : T_1 . T_2 :: *}\text{K-PI}$$

Although it does exist, but we can't construct a type of such kind inside the expression. Intuitively, by using the "dependent product type", we should be able to construct it. But actually, K-PI requires the $T_1$ and $T_2$ to be both of $*$ kind.

In fact, Benjamin mentioned in the text of 2.2 that

> the only way to construct an object of a kind other than $∗$ is by declaring it in the context

## Equivalence ane Reduction
The equivalence rules of `Kind`, `Type` and `Term` are recursively related. This is interesting. The reason is that, `KPi` includes `Type`, `TyApp` includes `Term`, and `TmAbs` includes `Type`.

Something is really strange here.

For example, 

```haskell
-- (QTA-VAR)
typeEquiv (TyVar x) (TyVar x') | x == x' = return ()
```
The rationale is that, *there is not type variable abstraction* in lambda LF. so the so-called *type variable* here is the globally free types, rather than undetermined bound type $t$ in $\Lambda t. term$.

However, we have term abstraction:
 Unless we evaluate/reduce the term, how can we say if they are equivalent? But the algorithm will not do an aggressive evaluation. For example,

```haskell
-- (QA-APP)
termEquiv (TmApp s1 t1) (TmApp s2 t2) = do
    s1 `termEquiv` s2
    t1 `termEquiv` t2
```

It is certainly not "correct", since while `(\(x, y) -> x) (1, True)` is equal to `(\(x, y) -> y) (True, 1)`, they are not equivalent in this way.

In the lambda LF, for terms, we uses $\beta$ and $\eta$ rules, the remaining rules are purely structural and express that equivalence is a congruence.

We can use Martin-Löf's definitional equality to fix this problem, certainly.

Algorithmically, the weak head reduction is used. $\lambda x .t \equiv s$ is reduced to $s \, x \equiv t$ (And symmetrically), so the head part of application is $\beta$-reduced.

To further study these part, we need to understand the limitation of such reduction.
