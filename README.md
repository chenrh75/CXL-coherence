# CXL coherence model in TLA+

The workspace contains the original Murphi model and its plain TLA+ translation.

- [msi_opt.m](eecs570_sample/msi_opt.m): retained Murphi source.
- [msi_opt.tla](eecs570_sample/msi_opt.tla): translated model.
- [msi_opt.cfg](eecs570_sample/msi_opt.cfg): source invariants and explicit errors.
- [msi_opt_smoke.cfg](eecs570_sample/msi_opt_smoke.cfg): type/representation smoke checks.
- [msi_opt_checks.tla](eecs570_sample/msi_opt_checks.tla) and
  [configuration](eecs570_sample/msi_opt_checks.cfg): focused translation checks.
- [Translation notes](eecs570_sample/msi_opt_tla.md): modeling choices, validation
  results, and commands using the root `tla2tools.jar`.

The source's unresolved protocol issues are preserved in the translation.
