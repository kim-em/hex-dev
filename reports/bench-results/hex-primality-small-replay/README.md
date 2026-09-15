# Small-certificate replay experiments

The final package comparison is `hex-compact-primecert-six-bit-kernel.json`:
four adjacent AB/BA pairs per input, 64 complete proof checks. It uses compact
PrimeCert certificates and a supplied Hex Curve448 certificate.

The other complete comparisons retain intermediate checker implementations.
The `corrected` record fixes the initial PrimeCert source-generation failure
for table leaves above 997; the incomplete initial record remains here.
Component profiles check individual terms with a fresh kernel checker. Failed
prototype builds are retained, including diagnostic output, and are excluded
from performance conclusions. Repeated component checks and different
implementations are not pooled with the final package comparison.

| Record | Outcome |
|---|---|
| [hex-compact-primecert-corrected-kernel.json](hex-compact-primecert-corrected-kernel.json) | 64 calls; 0 unsuccessful |
| [hex-compact-primecert-kernel.json](hex-compact-primecert-kernel.json) | 14 calls; 1 unsuccessful |
| [hex-compact-primecert-shared-replay-kernel.json](hex-compact-primecert-shared-replay-kernel.json) | 64 calls; 0 unsuccessful |
| [hex-compact-primecert-six-bit-kernel.json](hex-compact-primecert-six-bit-kernel.json) | 64 calls; 0 unsuccessful |
| [hex-compact-primecert-verify.json](hex-compact-primecert-verify.json) | source preparation / construction record |
| [hex-curve448-supply-setup-failure.json](hex-curve448-supply-setup-failure.json) | build exit 1; 0 component checks |
| [hex-curve448-supply.json](hex-curve448-supply.json) | build exit 0; 0 component checks |
| [hex-primitive-all-certificate-kernel.json](hex-primitive-all-certificate-kernel.json) | 64 calls; 0 unsuccessful |
| [hex-shift-all-certificate-kernel.json](hex-shift-all-certificate-kernel.json) | 64 calls; 0 unsuccessful |
| [hex-shift-single-all-certificate-kernel.json](hex-shift-single-all-certificate-kernel.json) | 64 calls; 0 unsuccessful |
| [hex-small-fast-replay-profile.json](hex-small-fast-replay-profile.json) | build exit 0; 520 component checks |
| [hex-small-fuel-profile.json](hex-small-fuel-profile.json) | build exit 0; 680 component checks |
| [hex-small-imported-prototype-profile.json](hex-small-imported-prototype-profile.json) | build exit 0; 760 component checks |
| [hex-small-kernel-profile.json](hex-small-kernel-profile.json) | build exit 0; 520 component checks |
| [hex-small-primitive-pock-profile.json](hex-small-primitive-pock-profile.json) | build exit 0; 520 component checks |
| [hex-small-primitive-table-profile.json](hex-small-primitive-table-profile.json) | build exit 0; 520 component checks |
| [hex-small-product-direct-profile.json](hex-small-product-direct-profile.json) | build exit 0; 720 component checks |
| [hex-small-product-one-profile.json](hex-small-product-one-profile.json) | build exit 0; 720 component checks |
| [hex-small-product-profile.json](hex-small-product-profile.json) | build exit 1; 720 component checks |
| [hex-small-product-sentinel-profile.json](hex-small-product-sentinel-profile.json) | build exit 0; 720 component checks |
| [hex-small-raw-profile.json](hex-small-raw-profile.json) | build exit 0; 640 component checks |
| [hex-small-shared-witness-fixed-profile.json](hex-small-shared-witness-fixed-profile.json) | build exit 1; 720 component checks |
| [hex-small-shared-witness-profile.json](hex-small-shared-witness-profile.json) | build exit 1; 720 component checks |
| [hex-small-shared-witness-typed-profile.json](hex-small-shared-witness-typed-profile.json) | build exit 0; 720 component checks |
| [hex-small-window-heldout-profile.json](hex-small-window-heldout-profile.json) | build exit 0; 2400 component checks |
| [hex-small-window-profile.json](hex-small-window-profile.json) | build exit 0; 2240 component checks |
