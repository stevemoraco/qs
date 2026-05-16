import { useState } from "react";
import { Link, Redirect, useLocation } from "wouter";
import { Shield, AlertCircle, Github, ExternalLink, Camera, MousePointerClick, TimerOff, EyeOff, UserX, MonitorOff, Key, Lock } from "lucide-react";
import {
  enrollDeviceVerification,
  generateDevicePasscode,
  isAuthenticated,
  loginWithPasskey,
  linkDeviceWithInvite,
  setAuthHandle,
  setDevicePasscode,
  setToken,
} from "@/lib/auth";
import { subscribeToPush } from "@/lib/pwa";

const GITHUB_URL = "https://github.com/stevemoraco/qs";

function normalizeCodeInput(value: string): string {
  return value.trim().replace(/^[@#]+/, "").toLowerCase();
}

const LOGIN_PRIVACY_FEATURES = [
  { icon: Camera, label: "Front-camera detection for nearby recording devices" },
  { icon: MousePointerClick, label: "Messages decrypt only while held, one at a time" },
  { icon: UserX, label: "Usernames and rooms stay codenamed until reveal" },
  { icon: TimerOff, label: "TTL keys are purged so old ciphertext becomes noise" },
  { icon: EyeOff, label: "Blur and background shields hide secure content" },
  { icon: MonitorOff, label: "Screenshot, screen-capture, and print friction" },
  { icon: Key, label: "Alias and invite codes scope discovery and access" },
  { icon: Lock, label: "Only the handle is typed; Face ID or your password manager unlocks the passkey" },
  { icon: Shield, label: "Fresh device sessions are issued and invalidated on logout" },
];

export default function Login() {
  const [, setLocation] = useLocation();
  const [handle, setHandle] = useState("");
  const [error, setError] = useState("");
  const [isPasskeyPending, setIsPasskeyPending] = useState(false);
  const [linkCode, setLinkCode] = useState("");
  const [isLinking, setIsLinking] = useState(false);

  const handleSubmit = async (e: React.FormEvent) => {
    e.preventDefault();
    setError("");
    const normalizedHandle = normalizeCodeInput(handle);
    if (!normalizedHandle) {
      setError("Enter your handle.");
      return;
    }
    try {
      setIsPasskeyPending(true);
      const data = await loginWithPasskey(normalizedHandle);
      setToken(data.token);
      setAuthHandle(data.authHandle);
      void subscribeToPush(data.token);
      setLocation("/app", { replace: true });
    } catch (err: unknown) {
      setError(err instanceof Error ? err.message : "Passkey login failed.");
    } finally {
      setIsPasskeyPending(false);
    }
  };

  const isLoading = isPasskeyPending;

  const handleLinkDevice = async (e: React.FormEvent) => {
    e.preventDefault();
    setError("");
    const code = normalizeCodeInput(linkCode);
    if (!code) {
      setError("Enter an invite code to link this device. Handles are for discovery only.");
      return;
    }
    try {
      setIsLinking(true);
      await enrollDeviceVerification();
      const passcode = generateDevicePasscode();
      const data = await linkDeviceWithInvite(code, passcode);
      setToken(data.token);
      setAuthHandle(data.authHandle);
      setDevicePasscode(passcode);
      void subscribeToPush(data.token);
      setLocation("/app", { replace: true });
    } catch (err: unknown) {
      setError(err instanceof Error ? err.message : "Could not link this device with that invite.");
    } finally {
      setIsLinking(false);
    }
  };

  if (isAuthenticated()) {
    return <Redirect to="/app" replace />;
  }

  return (
    <div className="min-h-screen bg-background flex items-center justify-center px-4 py-12">
      <div className="w-full max-w-sm">
        <div className="flex items-center gap-2 justify-center mb-10">
          <div className="w-8 h-8 bg-primary flex items-center justify-center">
            <Shield className="w-4 h-4 text-primary-foreground" />
          </div>
          <span className="font-mono font-bold tracking-widest text-sm">QUANTUMSHIELD</span>
        </div>

        <div className="border border-border/50 bg-card/50 p-8 backdrop-blur-sm">
          <div className="mb-8">
            <h1 className="font-mono font-bold text-xl tracking-tight">ACCESS TERMINAL</h1>
            <p className="font-mono text-xs text-muted-foreground mt-2">
              Authenticate to access your encrypted channels
            </p>
          </div>

          <form onSubmit={handleSubmit} className="space-y-5">
            <div>
              <label className="font-mono text-xs text-muted-foreground block mb-2 tracking-widest">
                HANDLE
              </label>
              <input
                type="text"
                value={handle}
                onChange={(e) => setHandle(e.target.value)}
                className="w-full bg-background border border-border px-3 py-2.5 font-mono text-sm text-foreground focus:outline-none focus:border-primary/60 transition-colors"
                placeholder="@your-handle"
                name="username"
                autoComplete="username"
                autoCapitalize="none"
                required
                data-testid="input-handle"
              />
            </div>

            {error && (
              <div className="flex items-center gap-2 text-destructive border border-destructive/30 bg-destructive/10 px-3 py-2" data-testid="text-error">
                <AlertCircle className="w-4 h-4 flex-shrink-0" />
                <span className="font-mono text-xs">{error}</span>
              </div>
            )}

            <button
              type="submit"
              disabled={isLoading}
              className="w-full bg-primary text-primary-foreground font-mono text-xs tracking-widest py-3 hover:bg-primary/90 transition-all disabled:opacity-50"
              data-testid="button-submit"
            >
              {isLoading ? "AUTHENTICATING..." : "LOG IN"}
            </button>
          </form>

          <div className="mt-6 pt-6 border-t border-border/50">
            <p className="font-mono text-xs text-muted-foreground text-center">
              No account?{" "}
              <Link href="/register" className="text-primary hover:underline">
                CREATE HANDLE
              </Link>
            </p>
          </div>
        </div>

        <form onSubmit={handleLinkDevice} className="mt-4 border border-border/50 bg-card/40 p-4 space-y-3">
          <div>
            <div className="font-mono text-xs text-primary tracking-widest">LINK THIS DEVICE</div>
            <p className="font-mono text-xs text-muted-foreground mt-1 leading-relaxed">
              Use a one-use invite code from an existing device. Public handles are for chat discovery, not login.
            </p>
          </div>
          <input
            value={linkCode}
            onChange={(e) => setLinkCode(e.target.value)}
            className="w-full bg-background border border-border px-3 py-2.5 font-mono text-sm focus:outline-none focus:border-primary/60"
            placeholder="invite code"
            autoCapitalize="none"
            data-testid="input-link-code"
          />
          <button
            type="submit"
            disabled={isLinking}
            className="w-full border border-primary/40 text-primary font-mono text-xs tracking-widest py-3 hover:bg-primary/10 transition-all disabled:opacity-50"
            data-testid="button-link-device"
          >
            {isLinking ? "LINKING DEVICE..." : "LINK WITH INVITE"}
          </button>
        </form>

        <div className="mt-4 border border-border/30 bg-card/20 px-4 py-3">
          <p className="font-mono text-xs text-muted-foreground text-center">
            <span className="text-primary">// </span>
            Your private keys never leave your device
          </p>
        </div>

        <div className="mt-4 border border-primary/20 bg-primary/5 px-4 py-4">
          <div className="font-mono text-xs text-primary tracking-widest mb-2">ETHOS</div>
          <p className="font-mono text-xs text-muted-foreground leading-relaxed">
            What is the most secure ideal form of truly ephemeral digital communication?
            QuantumShield is a working experiment to answer that with software communities
            can audit, improve, and rely on.
          </p>
          <a
            href={GITHUB_URL}
            target="_blank"
            rel="noreferrer"
            className="mt-4 inline-flex w-full items-center justify-center gap-2 border border-border bg-card/60 text-foreground font-mono text-xs tracking-widest py-3 hover:border-primary/50 transition-all"
          >
            <Github className="w-4 h-4" />
            VIEW GITHUB
            <ExternalLink className="w-3 h-3" />
          </a>
        </div>

        <div className="mt-4 border border-border/40 bg-card/20 px-4 py-4">
          <div className="font-mono text-xs text-primary tracking-widest mb-3">PRIVACY FEATURES</div>
          <div className="space-y-3">
            {LOGIN_PRIVACY_FEATURES.map(({ icon: Icon, label }) => (
              <div key={label} className="flex items-start gap-3">
                <Icon className="w-4 h-4 text-primary flex-shrink-0 mt-0.5" />
                <span className="font-mono text-xs text-muted-foreground leading-relaxed">{label}</span>
              </div>
            ))}
          </div>
        </div>
      </div>
    </div>
  );
}
