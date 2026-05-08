import erinImg from './pics/erin.jpg'
import mattImg from './pics/matt.jpg'

// PLACEHOLDER: All strings marked [FILL IN] should be replaced with real content.

export const aboutContent = {
  // PLACEHOLDER: describe the project goal
  goals: `In the Probably Approximately Correct (PAC) Learning model, we are given a labeling of data that we want our hypothesis to match. For a concept class, we want to know if we can reliably come up with a low error hypothesis given a batch of m datasamples. This project formalizes the VC dimension based sample complexity bound for PAC learning using the Double Sample Trick in Lean 4 with Mathlib4. The goal is to provide a machine-verified proof that a concept class with VC dimension d can be learned from O((d/ε)log(1/ε) + (1/ε)log(1/δ)) examples.`,

  authors: [
    { name: 'Erin Jaen', photoSrc: erinImg },
    { name: 'Matthew Sun', photoSrc: mattImg },
  ],
}

export const methodsContent = {
  // PLACEHOLDER: replace with the actual GitHub repository URL
  githubUrl: 'https://github.com/matt-suncy/MAM-final-project',
  githubLabel: 'GitHub',
}

export const thoughtsLessonsContent = {
  sections: [
    {
      // PLACEHOLDER: replace with section title
      title: 'Working with an AI Agent',
      // PLACEHOLDER: replace with section body
      body: 'Over the course of working with Claude Code, we found that it was very difficult for the AI agent to come up with the Lean formalizations than we had anticipated. The total token usage was approximately 700k and for more certain sections of the formalization, Claude would spend multiple sessions (approximately 44k tokens per session) just combing through Mathlib without writing anything to the file. The time and token usage needed were most likely due to the forced adherence to Mathlib that was specified in the formalization plan. Once it wrote something down, it was rarely incorrect, so the effort seems to have paid off. We also found that it was not as careful as we would have liked. It deviated from our intended proof strategy in a couple of key parts, and it never notified us of these changes. It also tended to write lemmas that seemed relevant to our intended proof strategy but were never used, as if it changed its mind along the way.',
    },
    {
      // PLACEHOLDER: replace with section title
      title: 'Interesting Mathematical Details',
      // PLACEHOLDER: replace with section body
      body: "As we were auditing the formalization, we realized that many precise mathematical constructions were abstracted away when we were learning PAC learning. Starting with the most basic definition: How should a concept be defined? The definition that Claude Code came up with is ''a measurable set over the sample space $X$''. In hindsight, this is an obvious definition since what we want from a concept is a set that assigns 1 to elements in it and 0 to elements that are not and we'd want to know this assignment for some $m$ samples. However, we are not familiar with measure theory and without having done this project, we would never have thought about this in a mathematically precise way. We can use this to define when a hypothesis disagrees with the target concept and by how much(so the error), which this serves as the foundation for our PAC learning framework. On the other hand, the probability theory sections felt more like a necessary obstacle to overcome in order to connect our formalization with Mathlib rather than something enlightening. Nonetheless, it was interesting to see how much Lebesgue integration it took to formalize a proof for $\\Pr[A] \\leq 2 \\cdot \\Pr[B]$, which only took half a page and a simple Chernoff bound in class. This was also a deviation from our intended proof strategy, which we will discuss in Section. The last piece of math we wanted to highlight was how the Sauer-Shelah lemma was incorporated into the formalization. Mathlib's proof of Sauer-Shelah is for finite set families but a PAC learning concept class can be infinite. Claude Code came up with a definition that restricts a concept class only to concepts that are relevant to some finite sample. This relatively simple bridge allowed the Sauer-Shelah lemma to be used exactly the way we intended, to provide a polynomial bound on the number of samples in terms of the VC dimension of the concept class. It was reassuring to see a part of the formalization that matched up so well with our intended proof strategy down to the details.",
    },
    {
      // PLACEHOLDER: replace with section title
      title: 'Deviations from Intended Proof Strategy',
      // PLACEHOLDER: replace with section body
      body: `In the formalization, there were two key changes from the initial formalization plan. Firstly, our intended strategy to get to $\\Pr[A] \\leq 2 \\cdot \\Pr[B]$ for $m \\geq \\frac{8}{\\varepsilon}$ was different. We intended to use the fact that $\\Pr[B] \\geq \\Pr[A] \\cdot \\Pr[B \\mid A]$ and that if Event A happens then the first part of Event B is satisfied. This allows us to apply a Chernoff bound over the probability that this bad hypothesis makes fewer than $\\frac{\\varepsilon m}{2}$ mistakes on $S_2$. Then with some algebraic manipulation, we can arrive at the result $\\Pr[B \\mid A] < \\frac{1}{2}$. Claude Code chose a much longer and more rigorous strategy but still similar in some elements. The following is a summary of the proof in the formalization:
    1. Define the $(S_1, S_2)$ as product space. This way they are two independent measures from the same sample measure of size $2m$. This way we can work with the two sets independently.
    2. The difference starts here with the consideration of all possible datasets $S_1$. Events A and B can then be written as the expected value (integral) over all possible $S_1$. This means that for this strategy, we need to show $\\Pr[A \\mid S_1] \\leq 2 \\cdot \\Pr[B \\mid S_1]$ for any fixed $S_1$.
    3. Now for any $S_1$, two cases need to be considered:
        a. $S_1$ witnesses Event A: The proof for this case is very similar to our intended strategy because it means the first part of Event B has already been satisfied and just like before we need to show that a bad hypothesis makes many errors ($\\geq \\frac{\\varepsilon m}{2}$). Instead of a Chernoff bound, Claude Code used Chebyshev's inequality instead. 
        b. $S_1$ doesn't witness Event A: This case is trivial since if no bad hypothesis is consistent with $S_1$ then $\\Pr[A \\mid S_1] = 0$. And obviously $0 \\le 2 \\cdot \\Pr(B \\mid S_1)$ holds.

The previous proof gets us $\\Pr[A] \\leq 2 \\cdot \\Pr[B]$ but now we need to show $\\Pr[B] \\leq \\frac{\\delta}{2}$. The way we originally intended to go about this proof was to use a combinatorial argument. Start with a dataset $S$ of $2m$ examples, which also means we have some random split $(S_1, S_2)$ as described earlier. Consider some fixed labeling of the examples in $S$ that's in the growth function $\\Pi_C(S)$ (remember that the growth function contains all possible labelings). Suppose that we have some hypothesis that mislabels $k \\geq \\frac{\\varepsilon m}{2}$ of $S$. Imagine we draw $m$ examples from $S$ without replacement to form $S_2$. What is the probability that all $k$ of the mislabeled examples are among the $m$ examples drawn to form $S_2$? The answer to this reveals a useful bound on the probability of this event for a fixed labeling:
$$
\\begin{aligned}
\\frac{\\binom{m}{k}}{\\binom{2m}{k}} &= \\frac{m(m - 1)...(m - k + 1)}{2m(2m - 1)...(2m - k + 1)} \\\\
&\\leq \\frac{1}{2^k}
\\end{aligned}
$$
If you apply a union bound over all possible labelings, you get $\\Pr[B] \\leq \\Pi_C(2m) \\cdot \\frac{1}{2^{\\frac{\\varepsilon m}{2}}}$ which is enough to get to the final result. Note that the union bound has to be over the number of labelings instead of hypotheses, since there could be infinite hypotheses. Claude Code actually did formalize this part but we suspect that it was never used because Lean requires typing and such an argument is unusable (as far as we can see) for real numbers. Remember, $k \\geq \\frac{\\varepsilon m}{2}$ where $\\varepsilon$ is a probability. Instead, Claude Code went with a strategy that undeniably works but does not feel in the spirit of what we originally intended. The following is a summary of the proof in the formalization:
    1. Reminder that Event B is where some hypothesis $h \\in \\mathcal{C}$ gets all of $S_1$ right and is wrong on $\\ge \\epsilon / 2 \\cdot m$ elements of $S_2$. Using the monotonicity of measure, the formalization proof discards the latter altogether.
    2. The probability that some bad $h_b$ gets all independently draw examples correct is $(1 - p)^m$, where $p$ is the true error of $h_b$. By definition of a bad hypothesis, $(1 - p)^m \\leq (1 - \\varepsilon)^m$.
    3. This is where the proof feels more \`\`brutish''. Claude Code uses a helper lemma that uses pure analysis to show that $(1 - \\varepsilon)^m \\leq (\\frac{1}{2})^{\\frac{\\varepsilon m}{2}}$.
    4. Apply a union bound over all possible labelings, $\\Pi_C(2m)$, just like in our intended strategy.

We want to note that Step 3 of the formalization proof is not conceptually complicated. It uses $1 - x \\leq e^{-x}$, which is an inequality we used all the time in class, just by nature of looking at error rates on i.i.d. samples. However, it doesn't feel as clever as the combinatorial argument. More importantly to us, it doesn't thematically fit with the rest of the proof because it discards how the bad hypothesis interacts with $S_2$ entirely. This is a major theorem, yet it didn't involve a key setup to the proof.`
    },
  ],
}
