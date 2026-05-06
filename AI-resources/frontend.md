## Resolved Design Decisions

### Framework
- **React 18 + Vite + TypeScript** + **Tailwind CSS** + **React Router v6**
- **reactflow v11** + **@dagrejs/dagre** — dependency graph with auto-layout (`rankdir: 'BT'`, main theorem at top)
- **react-syntax-highlighter** — Lean code display with custom Abyss-inspired dark style, `haskell` grammar

### Fonts
- **Website Title**: Caveat (Google Fonts) — handwritten/sketchy, thin, clean
- **All other text**: Inter (Google Fonts) — geometric, clean, not overly round

### Colors
| Role | Value |
|---|---|
| Page background | `#FAFAFA` |
| Heading text | `#111111` |
| Body / H3 text | `#444444` |
| Box border | `1px solid #111111` |
| Box shadow | `3px 3px 0 rgba(0,0,0,0.08)` |
| Regular node background | `#FFFFFF` |
| Highlighted node background | `#EEF3FF` |
| Code panel background | `#000C18` (Abyss) |

### Dependency Graph — Node Scope
- **All** public + private **lemmas / theorems / instances** (no `def` items)
- ~60 nodes, ~71 edges derived from explicit proof calls
- **Highlighted nodes** (`#EEF3FF` background):
  - Definitions.lean: `sampleMeasure_isProbability`
  - GhostSample.lean: `bernoulli_error_lower_bound`, `ghost_sample_bound`
  - Hypergeometric.lean: `hypergeometric_bound`
  - Symmetrization.lean: `symmetrization_bound`, `sample_size_bound`
  - Main.lean: `sauer_shelah_bound`, `pac_sample_complexity_bound`
- Private nodes render with italic label text
- `isHighlighted` and `isPrivate` flags in `frontend/src/data/graphData.ts` control all styling — change one flag per node, no component edits needed

### Definitions Box — Scope
- **All** `def` / `noncomputable def` items from all files, including private `errIndicator`
- 20 definitions total, in file order
- Clicking a code block opens the CodePopup panel

### Content Placeholders
All placeholder text is marked `// PLACEHOLDER:` in:
- `frontend/src/data/content.ts` — About goals, Methods columns, GitHub URL
- `frontend/src/data/definitions.ts` — definition descriptions
- `frontend/src/data/graphData.ts` — node labels and naturalLanguageStatement strings

### How to Run
```bash
cd frontend
npm install
npm run dev      # dev server at http://localhost:5173
npm run build    # production build (TypeScript check + Vite bundle)
```

---

## Goal

I have a formalization in Lean of the sample complexity of PAC learning. It is a dense multi-file proof since computational learning theory is minimally developed in Mathlib4. I want to create a website to show the dependencies of the lemmas/theorems from the formalization, provide human readable statements of those theorems, and connect the human readable theorems to lean code.

I have a style and general design in mind already. I want to create a visualization of this design (either by implementing the frontend structure right away or in Figma) and then implement this design (open to suggestions on which frameworks to use - but I have worked with React JS/tailwind/CSS/HTML before) so that it is compatible and flexible with the lean project.

Note: When I say “Main Theorem” or “main theorem” I mean in human language: “PAC Sample Complexity Bound” and the theorem in the lean project is: “theorem pac_sample_complexity_bound”.

## Pages

Each page + each component (in order top to bottom in how they appear on the page - exceptions are noted). Bolded items are actionable components/tied to lean project

1. Home Page: 
    1. **Navigation Icon**: (Main Theorem, About, Methods)
    2. Website title - “AI Formalization of the Sample Complexity Bound of PAC Learning” (font: Website Title)
    3. Author names: “Erin Jaen and Matthew Sun” (font: Paragraph)
    4. **Main Theorem Box**: Should look like an expanded **node** component, but with theorem name in Heading 2 font instead.
    5. **Definitions Box**
2. Main Theorem Page:
    1. **Navigation Icon**: Same location as main page (Home, About, Methods)
    2. Webpage Title: “Main Theorem” (font: Webpage Title)
    3. **Dependency Graph**
3. About Page: 
    1. **Navigation Icon**: (Home, Main Theorem, Methods)
    2. Webpage Title: “About” (font: Webpage Title)
    3. Goals: Centered title “Goals” (font: Heading 2), Then center-aligned paragraph below (font: Paragraph)
    4. Authors (?): Maybe include. Centered title “Authors” (font: Heading 2). Then two circle photos placed side-by-side underneath. Then author name centered underneath each photo (font: paragraph, but bold)
4. Methods Page:
    1. **Navigation Icon:** (Home, Main Theorem, About)
    2. Webpage Title: “Methods” (font: Webpage Title)
    3. Methods Section: Two text columns (side-by-side). First column titled Initial (font: Heading 3). Second column titled Final (font: Heading 3). Below each title are left-justified (according to the column) text boxes (font: paragraph).
    4. Github: Link to formalization repo (will be provided). Text “Github” (font: Heading 3)

## Components

These are items that have actions associated with them and/or tie back to lean code.

### Navigation Icon

Description: Small button with three horizontal lines (grey). Always in top right corner.

Action: Click to see names of other pages (listed vertically) in a small rectangular popup (fit to the size of the page name list, should slide out and stay right justified). Click on a page name to navigate to that page. Click outside of the icon/list to close the popup.

### Definitions Box

Description: Any part of the lean project that is a definition (def). I am not sure about this section. I think it could be a single large box, with a “Definitions” title centered at the top (lettering: Heading 2), then a bulleted list (lettering: Paragraph) of each human-readable definition name (in bold) (should be similar to the lean definition name, but with spaces and proper capitalization), then the human-readable definition (can be done manually - just keep a filler for now).

Lean: Just have the Lean code directly underneath the human-readable definition name and description (no actions needed for this component)

Example of how a definition should look:

- A **Concept C** : Human-readable definition to be filled in manually.
    
    ```python
    def Concept (X : Type*) [MeasurableSpace X] := { s : Set X // MeasurableSet s }
    ```
    

### Dependency Graph

Description: the meat and potatoes of the webpage. Actually shows the theorem/lemma dependencies. Each theorem/lemma is a “node” component. There is an edge (thin black arrow) between a theorem/lemma and each theorem/lemma (inside the project) that it calls on to complete its proof. The arrow should point from the theorem/lemma called to the theorem/lemma that calls it.

Appearance: I want the main theorem node at the top, then a layer of the nodes it depends on below it, then further layers continuing downwards (arrows are mostly vertical/pointing up). If there are layers that have dependencies within them, add mostly horizontal arrows between those nodes. Edge arrows should never cross over nodes, so leave plenty of room between each node. If there is not enough room for all the nodes of a given layer to have their titles in 1-2 lines, move some of the nodes down to their own layer with longer arrows.

**Node**

Should only have the natural language theorem/lemma title (font: Heading 3) centered in a rectangular box (black outline, inside white). These can use the lean theorem/lemma titles as a placeholder for now. Afterwards they may be changed.

Actions: 

- Hover over the node to get the natural language statement of the theorem/lemma (font: Paragraph). The natural language statement can be a placeholder filler for now. Should expand the rectangle to fit the natural language statement in 4-5 lines. Once hovering stops, the node shrinks again.
- Click on the node to get the side popup with the lean code for that theorem/lemma. Side popup should have scrollable lean code + whole popup should cover up anything on the page (i.e. nodes/edges/navigation icon).
- Click out of the side popup (anywhere on background) to minimize the lean popup.

## Style

- Super clean, super simple, consistent appearance. Follow good design practices if you know them.
- Should be laptop/computer compatible format
- Background to be white, or something close to white.
- All items should be centered in whichever item they appear in.
- Lettering: thin, black (or dark grey), clean, I don’t love round looking letters. I am open to suggestions. Make sure it is clearly readable. No box around text unless otherwise specified
    - Website Title:  The only special font. I want a very large, almost cursive/sketchy font, but clean, thin and black, and centered on the top of the page. Open to suggestions for exact font, or I could try to input my own design. Should take up about a third of the page.
        - Webpage title: bold, should have the same size font as the website title, but should be the normal font (should use the same lettering)
    - Heading 2: Black, bold font, large, but smaller than the webpage titles
    - Heading 3: Dark grey, bold, medium size
    - Paragraph: Dark grey, smallest size (but not too small - should still be readable)
- Any boxes or outlines should be thinly outlined, black rectangles with sharp corners, should look like they are hovering slightly on top of the page.
- Do not overcrowd: can and should have scrolling option for each page. There should be plenty of white space between all text/items on the page.
- Code pop-up: appears on a right side pop-up (should be about a fourth of the screen horizontally, fill the screen vertically) (background still white, should look like it appears on top of the current page, ) The lean code itself should be in a dark mode style (I like the “Abyss” theme in VS Code) coding box centered inside the popup (potentially the lean code box is scrollable since the theorems/lemmas could be long, should not be editable).

## Important Notes

- Currently there is some refactoring in the lean formalization to be done. I would like for the frontend to be reliant only on the current state of the lean code (so frontend structure is not reliant on the current state - it does not need to be an instantaneous change in the frontend with every lean update, but do not hard code in the current theorems/lemms/dependencies).
- Nothing appearing in the frontend should be editable in the frontend (protect the formalization code) - this is a visualization project only.
- The frontend design should have be pretty easy to tweak if necessary and any change keeps website consistency
- Current plan is to implement frontend in the same repo as the lean formalization. Make sure the lake configurations and frontend related resources never mix. I.e. frontend should be in its own folder. This is super important.