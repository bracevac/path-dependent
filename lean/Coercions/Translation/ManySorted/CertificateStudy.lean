import Coercions.Translation.ManySorted.CertificateStudy.Metrics
import Coercions.Translation.ManySorted.CertificateStudy.MetricsExamples
import Coercions.Translation.ManySorted.CertificateStudy.NormalizationMetrics
import Coercions.Translation.ManySorted.CertificateStudy.NormalizationMetricsExamples
import Coercions.Translation.ManySorted.CertificateStudy.ReadOnlyBenchmark
import Coercions.Translation.ManySorted.CertificateStudy.ReadOnlyBenchmarkExamples

/-!
# Checked-certificate case study

This aggregate contains the reproducible size and adapter-overhead counters,
the check-normalize-recheck evidence pass, and the Capybara-inspired
read-only separation program.  The benchmark exercises capture abstraction,
same-root read-only separation, a repeated-label object signature, explicit
object opening, and independently checked ManySortedFC output.  It models
static access separation only; it does not add concurrency, allocation,
mutation, consumption, or freshness to the shared runtime.
-/
