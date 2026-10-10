# COMPX361 Test 2 Trainer

An unofficial study tool for **COMPX361 Logic and Computation (University of Waikato), Test 2**. It lets you practise every process on the test one step at a time, and checks each step as you go.

**Live site: https://officialprotondev.github.io/COMPX361-Test-2-Trainer/**

## What's in it

- **24 checked drills** across Turing machines, grammars and automata, propositional logic, predicate logic and induction. The checking covers truth-table cells, each law in a proof, every line of induction working, each derivation step, and each grammar against every short string.
- **A study plan** on the overview, ranked by the marks each question type was worth in the 2023–25 papers (2025 counted double), that shows your progress and what to do next.
- **Past papers**: the 2023–2025 Test 2 papers and tutorials 5–9, with the lecturer's solutions.
- **Mock tests**: a fresh 60-minute, 40-mark paper in the format of a past test, marked when you submit.
- **Reference sheets**: the Turing code table and the laws of equivalence (both supplied in the test), plus the course's conventions.

Your progress is saved in your own browser only. There's no account and no server.

On this site you mark written answers against a checklist. The copy hosted on Claude, which the site links to, can also mark them with Claude, using your own Claude account.

## Development

Needs Node 20 or later.

```sh
npm ci
npm test        # checker and mock-test tests (node:test)
npm run build   # dist/site/index.html for GitHub Pages, dist/index.html for the Claude-hosted copy
```

The app uses Preact, and esbuild bundles it into a single self-contained HTML file. The source is organised like this:

- `src/engines/`: the checkers (propositional and predicate logic, grammars and automata, induction, Turing codes and more)
- `src/data/`: the question banks and the past papers
- `src/ui/`: the pages and drills

## Deployment

Every push to `main` runs `.github/workflows/pages.yml`. It installs the dependencies, runs the tests, builds the site and deploys `dist/site` to GitHub Pages. If a test fails, nothing is deployed.

## Notes

This tool wasn't produced or checked by the course staff. The past papers, tutorial questions and solutions belong to their authors. Earlier years' tests may not cover exactly the same scope as this year's.
