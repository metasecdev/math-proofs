# metasecdev/math-proofs: audit + go-public plan (prepared 2026-11-01; status updated 2026-11-01 ~2 PM ET)

## Status
- DONE: Brian chose Apache-2.0 for code; OK to publish metasecdev@gmail.com in history.
- DONE: paper PRs #14, #15 merged (main cd0d45e).
- DONE (step 2): PR #16 `release/license-citation`: LICENSE (Apache-2.0, Copyright 2026 Brian Bernard Taylor), NOTICE, CITATION.cff (cffconvert-valid), .zenodo.json (no arXiv placeholder), README License + How to cite, generator cache path made relative. Lean CI passed (build 25m59s; Paper workflow not triggered, no paper/ changes); merged as fe01afe. GitHub detects Apache-2.0.
- DONE (step 3): repo description updated (wiki/issues left on).
- Repo still PRIVATE; Zenodo not enabled; no v1.0.1 tag/release.
- TODO at tag time: set CITATION.cff date-released (currently 2026-11-01 placeholder) to the real tag date.

## Audit summary
- gitleaks 8.21.2 over `--all` history: no leaks. Regex scan of `git log --all -p` (38 commits, 15 remote branches, tag v1.0.0): no keys/tokens/passwords/private IPs/Tailscale/.local hostnames/`/Users/`/`/home/` paths.
- Largest blob: paper/main.pdf 169 KB. No blob > 200 KB.
- Commit identities that go public: `metasecdev <metasecdev@gmail.com>` (14 commits, GitHub web-merge commits) and `metasecdev <metasecdev@users.noreply.github.com>` (24).
- Low-severity items (no history rewrite needed):
  1. lean_tools/gen_fast_guard_all.py:40-41 hard-codes `/workspace/fast_g_*.json` cache paths (from commit 62c334a). Harmless; optional fix: make them relative.
  2. Provenance notes name private repos metasecdev/irrational-gap-mobius and metasecdev/igm-clean (commit messages of the import commits, lakefile.lean comment, file headers, README Provenance). Names only, no contents. Readers will see 404s; fine to keep.
  3. reports/heavy-certs-2026-10-31.md and README describe the build machine (MacBook Pro 16,1, i9-9980HK, 64 GB, macOS 26.6.2). No hostname/username. Fine to keep.
  4. GitHub repo description says "owned by the Math Proofs bot; copied from irrational-gap-mobius": update before going public.
  5. v1.0.0 release notes say "The repository is private." Edit after going public.
- No P vs NP / SAT / non-BBP material in any commit (SAT/Twist pieces were removed before the first import commit, so they are not in history).
- PRs #1-#15 bodies, comments, review comments: nothing sensitive. No issues. No Actions secrets or variables. 57 workflow runs; artifacts are only axioms-report and paper-pdf. Once public, all run logs become publicly readable and artifacts downloadable by signed-in users; a sample log has no secrets/paths.
- Wiki and Issues are enabled (empty).

## Licensing
- Paper: paper/LICENSE-CC-BY-4.0 (CC BY 4.0).
- Code: NO LICENSE file at the repo root, and GitHub detects none. Without one, the public code is "all rights reserved". Recommended: Apache-2.0 (same license as Mathlib/Lean). Brian has to choose.

## Steps
1. DONE: paper PRs #14, #15 merged.
2. DONE: PR #16 merged (fe01afe). Remaining: set date-released at tag time.
3. DONE: repo description updated.
4. **Brian go #1 (irreversible in practice):** `gh repo edit metasecdev/math-proofs --visibility public --accept-visibility-change-consequences`. Once anyone clones or forks, the full history (all branches, author emails above) is permanent.
5. **Brian personally:** sign in at zenodo.org with GitHub, Settings > GitHub. metasecdev/math-proofs is under a personal account here (no org), so no org OAuth grant is needed; if it ever moves to an org, the org has to approve the Zenodo OAuth app. Click Sync, flip the switch for metasecdev/math-proofs. Only releases published AFTER this point are archived (v1.0.0 will not be).
6. Tag v1.0.1 on main (annotated) and **Brian go #2 (irreversible):** publish GitHub release v1.0.1. Zenodo archives the zip and mints a concept DOI (all versions) and a version DOI (v1.0.1). A published Zenodo version cannot be deleted; only new versions can be added (or metadata edited).
7. Check the record on zenodo.org (title, creator, license, description). Edit metadata there if needed.
8. PR: add the DOI to paper/main.tex (Repository section + refs.bib entry, cite the version DOI for exact reproducibility, the concept DOI for "latest"), add `doi:` to CITATION.cff, add a DOI badge to README, refresh main.pdf. Edit v1.0.0 release notes to drop "The repository is private."
9. After arXiv: add the arXiv ID to CITATION.cff preferred-citation and to the Zenodo record's related identifiers (metadata edit, no new version needed).
