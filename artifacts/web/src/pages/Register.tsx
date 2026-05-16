import { useEffect, useState } from "react";
import { Link, useLocation } from "wouter";
import { Shield, AlertCircle, CheckCircle, Loader } from "lucide-react";
import { usePostAuthRegister, usePostKeysUpload } from "@workspace/api-client-react";
import { setToken, storeKeyPair } from "@/lib/auth";
import { subscribeToPush } from "@/lib/pwa";
import { ml_kem1024 } from "@noble/post-quantum/ml-kem.js";
import { ml_dsa87 } from "@noble/post-quantum/ml-dsa.js";

function uint8ToBase64(arr: Uint8Array): string {
  return btoa(String.fromCharCode(...arr));
}

function extractErrorMessage(err: unknown, fallback: string): string {
  if (err && typeof err === "object") {
    const e = err as { response?: { data?: { error?: unknown } }; message?: unknown };
    const apiErr = e.response?.data?.error;
    if (typeof apiErr === "string" && apiErr.length > 0) return apiErr;
    if (typeof e.message === "string" && e.message.length > 0) return e.message;
  }
  return fallback;
}

type GenerationStep =
  | "idle"
  | "generating-kem"
  | "generating-dsa"
  | "submitting"
  | "uploading"
  | "done";

export default function Register() {
  const [, setLocation] = useLocation();
  const [username, setUsername] = useState("");
  const [password, setPassword] = useState("");
  const [displayName, setDisplayName] = useState("");
  const [error, setError] = useState("");
  const [step, setStep] = useState<GenerationStep>("idle");

  const register = usePostAuthRegister();
  const uploadKeys = usePostKeysUpload();

  useEffect(() => {
    const params = new URLSearchParams(window.location.search);
    const email = params.get("email") ?? "";
    const name = params.get("name") ?? "";
    let savedName = "";

    try {
      const saved = localStorage.getItem("qs_invite_profile");
      if (saved) {
        const parsed = JSON.parse(saved) as { name?: unknown; email?: unknown };
        if (!email && typeof parsed.email === "string") {
          const candidate = parsed.email.split("@")[0]?.replace(/[^a-zA-Z0-9_-]/g, "").slice(0, 32);
          if (candidate && candidate.length >= 3) setUsername(candidate.toLowerCase());
        }
        if (typeof parsed.name === "string") savedName = parsed.name;
      }
    } catch {
      // Ignore malformed local invite state.
    }

    if (email) {
      const candidate = email.split("@")[0]?.replace(/[^a-zA-Z0-9_-]/g, "").slice(0, 32);
      if (candidate && candidate.length >= 3) setUsername(candidate.toLowerCase());
    }
    if (name || savedName) setDisplayName(name || savedName);
  }, []);

  const handleSubmit = async (e: React.FormEvent) => {
    e.preventDefault();
    setError("");

    setStep("generating-kem");
    const kem = ml_kem1024.keygen();

    setStep("generating-dsa");
    const dsa = ml_dsa87.keygen();

    const kemPkB64 = uint8ToBase64(kem.publicKey);
    const dsaPkB64 = uint8ToBase64(dsa.publicKey);

    let token: string;
    try {
      setStep("submitting");
      const authData = await register.mutateAsync({
        data: {
          username,
          password,
          displayName: displayName || undefined,
          kemPublicKey: kemPkB64,
          dsaPublicKey: dsaPkB64,
        },
      });
      token = authData.token;
      storeKeyPair(kem.secretKey, kem.publicKey, dsa.secretKey, dsa.publicKey);
      setToken(token);
    } catch (err: unknown) {
      setStep("idle");
      setError(extractErrorMessage(err, "Could not create identity. Please try a different username."));
      return;
    }

    try {
      setStep("uploading");
      const kemSig = ml_dsa87.sign(kem.publicKey, dsa.secretKey);
      await uploadKeys.mutateAsync({
        data: {
          kemPublicKey: kemPkB64,
          dsaPublicKey: dsaPkB64,
          kemSignature: uint8ToBase64(kemSig),
        },
      });
    } catch (err: unknown) {
      setStep("idle");
      setError(extractErrorMessage(err, "Identity created, but key bundle upload failed. Please log in and retry."));
      return;
    }

    // Best-effort push subscription — non-blocking failures.
    void subscribeToPush(token);

    setStep("done");
    setLocation("/app");
  };

  const stepLabels: Record<GenerationStep, string> = {
    idle: "CREATE IDENTITY",
    "generating-kem": "GENERATING ML-KEM-1024 KEYS...",
    "generating-dsa": "GENERATING ML-DSA-87 KEYS...",
    submitting: "REGISTERING IDENTITY...",
    uploading: "UPLOADING KEY BUNDLE...",
    done: "COMPLETE",
  };

  const isLoading = step !== "idle";

  return (
    <div className="min-h-screen bg-background flex items-center justify-center px-4">
      <div className="w-full max-w-sm">
        <div className="flex items-center gap-2 justify-center mb-10">
          <div className="w-8 h-8 bg-primary flex items-center justify-center">
            <Shield className="w-4 h-4 text-primary-foreground" />
          </div>
          <span className="font-mono font-bold tracking-widest text-sm">QUANTUMSHIELD</span>
        </div>

        <div className="border border-border/50 bg-card/50 p-8 backdrop-blur-sm">
          <div className="mb-8">
            <h1 className="font-mono font-bold text-xl tracking-tight">REQUEST CLEARANCE</h1>
            <p className="font-mono text-xs text-muted-foreground mt-2">
              Post-quantum key pairs are generated locally — your private keys never leave this device
            </p>
          </div>

          <form onSubmit={handleSubmit} className="space-y-5">
            <div>
              <label className="font-mono text-xs text-muted-foreground block mb-2 tracking-widest">
                IDENTIFIER
              </label>
              <input
                type="text"
                value={username}
                onChange={(e) => setUsername(e.target.value)}
                className="w-full bg-background border border-border px-3 py-2.5 font-mono text-sm text-foreground focus:outline-none focus:border-primary/60 transition-colors"
                placeholder="username (min 3 chars)"
                autoComplete="username"
                minLength={3}
                maxLength={32}
                required
                disabled={isLoading}
                data-testid="input-username"
              />
            </div>

            <div>
              <label className="font-mono text-xs text-muted-foreground block mb-2 tracking-widest">
                DISPLAY NAME (OPTIONAL)
              </label>
              <input
                type="text"
                value={displayName}
                onChange={(e) => setDisplayName(e.target.value)}
                className="w-full bg-background border border-border px-3 py-2.5 font-mono text-sm text-foreground focus:outline-none focus:border-primary/60 transition-colors"
                placeholder="Display name"
                disabled={isLoading}
                data-testid="input-display-name"
              />
            </div>

            <div>
              <label className="font-mono text-xs text-muted-foreground block mb-2 tracking-widest">
                PASSPHRASE
              </label>
              <input
                type="password"
                value={password}
                onChange={(e) => setPassword(e.target.value)}
                className="w-full bg-background border border-border px-3 py-2.5 font-mono text-sm text-foreground focus:outline-none focus:border-primary/60 transition-colors"
                placeholder="min 8 characters"
                autoComplete="new-password"
                minLength={8}
                required
                disabled={isLoading}
                data-testid="input-password"
              />
            </div>

            {error && (
              <div className="flex items-center gap-2 text-destructive border border-destructive/30 bg-destructive/10 px-3 py-2" data-testid="text-error">
                <AlertCircle className="w-4 h-4 flex-shrink-0" />
                <span className="font-mono text-xs">{error}</span>
              </div>
            )}

            {isLoading && (
              <div className="flex items-center gap-2 text-primary border border-primary/30 bg-primary/10 px-3 py-2">
                <Loader className="w-4 h-4 flex-shrink-0 animate-spin" />
                <span className="font-mono text-xs">{stepLabels[step]}</span>
              </div>
            )}

            <button
              type="submit"
              disabled={isLoading}
              className="w-full bg-primary text-primary-foreground font-mono text-xs tracking-widest py-3 hover:bg-primary/90 transition-all disabled:opacity-50"
              data-testid="button-submit"
            >
              {stepLabels[step]}
            </button>
          </form>

          <div className="mt-6 pt-6 border-t border-border/50">
            <p className="font-mono text-xs text-muted-foreground text-center">
              Already have access?{" "}
              <Link href="/login" className="text-primary hover:underline">
                AUTHENTICATE
              </Link>
            </p>
          </div>
        </div>

        <div className="mt-4 border border-primary/20 bg-primary/5 px-4 py-3 space-y-1">
          {[
            "ML-KEM-1024 keys generated in your browser",
            "ML-DSA-87 identity keys generated locally",
            "Private keys stored only in your device",
          ].map((note) => (
            <div key={note} className="flex items-center gap-2">
              <CheckCircle className="w-3 h-3 text-primary flex-shrink-0" />
              <span className="font-mono text-xs text-muted-foreground">{note}</span>
            </div>
          ))}
        </div>
      </div>
    </div>
  );
}
