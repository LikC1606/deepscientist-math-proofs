# In-Progress LeanEval Proofs

Snapshots of all three active problems, including all four agent worktrees per problem:

| Problem | Snapshot |
| --- | --- |
| Dimitrov | [dimitrov](dimitrov/) |
| Hopf-Rinow | [hopf_rinow](hopf_rinow/) |
| Szemeredi | [szemeredi](szemeredi/) |

[snapshot.json](snapshot.json) records capture times and progress. Each problem contains:

- `workers/<agent>/`: current Lean sources, dependency pins, research notes, cooperation state, and delivery journals.
- `state.json`: the runtime checkpoint, including task states, existing verification receipts, failures, and cumulative usage.
- `manifest.json`: source provenance, worker metadata, and SHA-256 hashes of all archived files.
- `history.fast-export.gz`: historical proof and research revisions from the run's Git repository, filtered to these source files. The export includes `original-oid` metadata; importing it creates new commit IDs.
- `task*.md`: the original task and continuation instructions when present.

These drafts may contain `sorry`, failed approaches, and unchecked changes. Only the separately archived accepted packages have official acceptance. A local helper check does not establish that an entire problem is solved.

Solvers continued running during capture. Files are individually stable snapshots, but the checkpoint and worktrees can reflect nearby instants. Absolute paths in records refer to the original host. Runtime binaries, model conversations, credentials, environment files, and Lean caches are omitted.

To inspect the filtered history in a separate directory:

```sh
git init recovered
gzip -dc dimitrov/history.fast-export.gz | git -C recovered fast-import --force
git -C recovered branch -a
```

For Lean checks, use the matching original generated workspace and the dependency pins under each agent's project directory. The snapshots preserve research progress; they are not complete machine-independent runtime backups.
