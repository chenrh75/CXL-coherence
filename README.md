# CXL coherence model in TLA+

The workspace contains a corrected plain TLA+ model and its historical Murphi source.

- [msi_opt.tla](eecs570_sample/msi_opt.tla): message-oriented coherence model.
- [msi_opt.m](eecs570_sample/msi_opt.m): retained historical Murphi reference.
- [Model notes and verification commands](eecs570_sample/msi_opt_tla.md).
- [Issue investigation and repair status](eecs570_sample/msi_opt_issues.md).
- [Protocol reference](CXL-cache-protocol-reference.md).
- [Regression runner](eecs570_sample/msi_opt_audit.py): safety and eventual drain checks;
  supports `--workers` and `--ids`.

The literal translation before protocol repairs is available in git commit `eafe09e`.
