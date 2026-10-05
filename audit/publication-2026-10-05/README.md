# Publication preparation checks

This directory records checks of the added repository presentation. It is separate from the original proof audit in `audit/2026-10-05/`.

`presentation-checks.json` records:

- 303 sampled states compared with the preserved independent Python simulator: boards, positions, headings and read colors all match.
- All 101 decoded GIF frames match the renderer, including the optimized frame disposal; the 16.75-second animation is about 239 kB.
- All 89 original Lean files, the original toolchain/configuration and manuscript still match their source hashes.
- Python syntax, manual CI workflow structure and local document links pass the recorded checks.

Initial, exploration and highway frames were visually inspected. The GIF has no role in the proof. The GitHub workflow has been syntax-checked; this record does not claim a completed GitHub-hosted build. The original fresh Lean source build remains the recorded proof validation.

The repository was published through GitHub's browser interface. Validation commands invoke Bash explicitly and Python helpers invoke Python explicitly, so they work without executable file permissions. After uploading, the published Git tree is compared with the maintained source tree; original proof and paper hashes are checked again.

`github-verification.json` records the comparison of the complete initial publication commit: all 238 paths, file contents and modes match the prepared source commit. The 89 original Lean source files, two original configuration files and original manuscript match their source SHA-256 values. No build or Python cache files are present. This verification record is added after the commit it verifies.
