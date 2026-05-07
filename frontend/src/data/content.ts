// PLACEHOLDER: All strings marked [FILL IN] should be replaced with real content.

export const aboutContent = {
  // PLACEHOLDER: describe the project goal
  goals: `In the Probably Approximately Correct (PAC) Learning model, we are given a labeling of data that we want our hypothesis to match. For a concept class, we want to know if we can reliably come up with a low error hypothesis given a batch of m datasamples. This project formalizes the VC dimension based sample complexity bound for PAC learning using the Double Sample Trick in Lean 4 with Mathlib4. The goal is to provide a machine-verified proof that a concept class with VC dimension d can be learned from O((d/ε)log(1/ε) + (1/ε)log(1/δ)) examples.`,

  authors: [
    { name: 'Erin Jaen', photoSrc: '' },   // PLACEHOLDER: set photoSrc to an image path or URL
    { name: 'Matthew Sun', photoSrc: '' }, // PLACEHOLDER: set photoSrc to an image path or URL
  ],
}

export const methodsContent = {
  // PLACEHOLDER: replace with the actual GitHub repository URL
  githubUrl: 'https://github.com/[FILL IN]/MAM-final-project',
  githubLabel: 'GitHub',
}

export const thoughtsLessonsContent = {
  sections: [
    {
      // PLACEHOLDER: replace with section title
      title: '[FILL IN] Section Title 1',
      // PLACEHOLDER: replace with section body
      body: '[FILL IN] Paragraph text for section 1.',
    },
    {
      // PLACEHOLDER: replace with section title
      title: '[FILL IN] Section Title 2',
      // PLACEHOLDER: replace with section body
      body: '[FILL IN] Paragraph text for section 2.',
    },
    {
      // PLACEHOLDER: replace with section title
      title: '[FILL IN] Section Title 3',
      // PLACEHOLDER: replace with section body
      body: '[FILL IN] Paragraph text for section 3.',
    },
  ],
}
