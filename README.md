# MAM-final-project

Formalizing the double sample argument for the sample complexity upper bound of PAC learning.

## The Goal

The objective is to formalize the sample complexity upper bound for PAC learning. Specifically, you must prove that for a concept class $\mathcal{C}$ and a target concept $c$, given a dataset $S_1$ of $m$ examples drawn from $EX(c, \mathcal{D})$, if the sample size $m$ satisfies both $m \ge \frac{8}{\epsilon}$ and $m \ge \frac{2}{\epsilon}(\log(\Pi_\mathcal{C}(2m)) + \log\frac{2}{\delta})$, then with probability at least $1-\delta$, all bad hypotheses $h \in \mathcal{C}$ (where $error(h) \ge \epsilon$) are inconsistent with the dataset. By applying the bound on the growth function $\Pi_\mathcal{C}(2m)$, this eventually simplifies to the overarching theorem that $m \ge c_0(\frac{1}{\epsilon}\log\frac{1}{\delta} + \frac{d}{\epsilon}\log\frac{1}{\epsilon})$ examples are sufficient.}

## The Double Sample Argument

Let $D$ be a distribution over the domain $X \times \{0,1\}$. Draw $2m$ samples from $EX[c, D]$, an oracle for a target concept $c \in \mathcal{C}$. Call the first $m$ samples $S_1$ and second $m$ samples $S_2$. Consider events $A, B$
\begin{itemize}
    \item $A:$ some hypothesis $h \in \mathcal{C}$ with error-rate $> \epsilon$ on the distribution gets all of $S_1$ right.
    \item $B:$ some hypothesis $h \in \mathcal{C}$ gets all of $S_1$ right and is wrong on $\ge \epsilon/2\cdot m$ elements of $S_2$
\end{itemize}
The Double Sample argument argues that for $m \ge 8/\epsilon$, $\Pr[A] \le \Pr[B]$. This shows that any hypothesis with a true error rate greater than $\epsilon$ is unlikely to be consistent with $S_1$, which is the requirement for PAC learning.

