<H1>Clock Model: Formal View</H1>

# Clocks

Assume there exists an enumerable set $\mathcal{C}$ of atomic entities called clocks.<br/>
Assume also the Leibniz equality for clocks is decisive, that is, for any two clocks $c_1$ and $c_2$, one can prove whether $c_1=c_2$ or $c_1\neq c_2$.

Enumerability of $\mathcal{C}$ guarantees the existence of a bijection between $\mathcal{C}$ and the set of natural number $\mathbb{N}$.<br/>
We fix one of such a bijection and denote it by $\mathop{\mathrm{toNat}}:\mathcal{C}\to\mathbb{N}$.
We use the notation $\mathop{\mathrm{nthClock}}$ for the function $\mathop{\mathrm{toNat}}^{-1}:\mathbb{N}\to\mathcal{C}$.

Given these considerations, we model the set of all clocks as the following inductive type.

```
Inductive clock : Set := nthClock : nat -> clock.
````

Also, we define the coercion as follows

```
Coercion toNat := fun c : clock => let 'nthClock n := c in n.
```

# Clock Sets

Also, we consider finite sets of clocks, which are called clock sets.
For referring to the set of all clock sets, the denotation $[\mathcal{C}]^{<\omega}$ is used.
