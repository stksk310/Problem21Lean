# C10 verification inputs

`generate_euclidean_certificate.py` reads the frozen supplement ZIP directly. It validates the ZIP, both byte-identical coefficient tables, the frozen verifier, its committed result and stdout, and the 3234-term table shape before emitting transparent Lean data.

Generate the data with the workspace Python runtime:

```powershell
python verification/c10/generate_euclidean_certificate.py
```

CI uses `--check` to regenerate the expected bytes in memory and reject drift in any committed `GeneratedTerminalCertificate*.lean` file.
