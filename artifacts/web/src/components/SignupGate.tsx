import { useEffect, useState } from "react";
import { Shield, Download, Bell, CheckCircle, AlertCircle, Loader } from "lucide-react";
import {
  isStandalone,
  canPromptInstall,
  promptInstall,
  onInstallStateChange,
  notificationPermission,
  requestNotificationPermission,
} from "@/lib/pwa";

type Props = {
  children: React.ReactNode;
};

export default function SignupGate({ children }: Props) {
  const [installed, setInstalled] = useState(isStandalone());
  const [canPrompt, setCanPrompt] = useState(canPromptInstall());
  const [perm, setPerm] = useState<NotificationPermission | "unsupported">(notificationPermission());
  const [busy, setBusy] = useState<"install" | "notif" | null>(null);
  const [error, setError] = useState("");

  useEffect(() => {
    const unsub = onInstallStateChange(() => {
      setInstalled(isStandalone());
      setCanPrompt(canPromptInstall());
    });
    const handler = () => setInstalled(isStandalone());
    const mq = window.matchMedia("(display-mode: standalone)");
    mq.addEventListener?.("change", handler);
    return () => {
      unsub();
      mq.removeEventListener?.("change", handler);
    };
  }, []);

  const notifGranted = perm === "granted";
  const ready = installed && notifGranted;

  if (ready) return <>{children}</>;

  const handleInstall = async () => {
    setError("");
    setBusy("install");
    const outcome = await promptInstall();
    setBusy(null);
    if (outcome === "unavailable") {
      setError(
        "Your browser hasn't offered an install prompt yet. On iOS Safari, tap the Share button and choose \"Add to Home Screen\". On Chrome/Edge, look for the install icon in the URL bar.",
      );
    } else if (outcome === "dismissed") {
      setError("Install was dismissed. Please install QuantumShield to continue.");
    }
  };

  const handleNotifs = async () => {
    setError("");
    setBusy("notif");
    const result = await requestNotificationPermission();
    setBusy(null);
    setPerm(result);
    if (result === "denied") {
      setError(
        "Notifications were blocked. Open your browser settings for this site and allow notifications, then refresh.",
      );
    } else if (result === "unsupported") {
      setError("This browser does not support notifications. Try Chrome, Edge, or Safari.");
    }
  };

  return (
    <div className="min-h-screen bg-background flex items-center justify-center px-4 py-12">
      <div className="w-full max-w-md">
        <div className="flex items-center gap-2 justify-center mb-10">
          <div className="w-8 h-8 bg-primary flex items-center justify-center">
            <Shield className="w-4 h-4 text-primary-foreground" />
          </div>
          <span className="font-mono font-bold tracking-widest text-sm">QUANTUMSHIELD</span>
        </div>

        <div className="border border-border/50 bg-card/50 p-8 backdrop-blur-sm">
          <div className="mb-8">
            <h1 className="font-mono font-bold text-xl tracking-tight">SECURE CHANNEL REQUIRED</h1>
            <p className="font-mono text-xs text-muted-foreground mt-2 leading-relaxed">
              Before requesting clearance, install QuantumShield as an app and enable encrypted push
              alerts. Both steps are required to deliver out-of-band ciphertext.
            </p>
          </div>

          <ol className="space-y-4">
            <li className="border border-border/60 bg-background/40 p-4">
              <div className="flex items-start gap-3">
                <div
                  className={`w-6 h-6 flex items-center justify-center flex-shrink-0 mt-0.5 ${
                    installed ? "bg-primary/20" : "bg-muted"
                  }`}
                >
                  {installed ? (
                    <CheckCircle className="w-4 h-4 text-primary" />
                  ) : (
                    <Download className="w-3.5 h-3.5 text-muted-foreground" />
                  )}
                </div>
                <div className="flex-1 min-w-0">
                  <div className="font-mono text-xs font-semibold tracking-widest">
                    STEP 1 · INSTALL APP
                  </div>
                  <p className="font-mono text-xs text-muted-foreground mt-1">
                    {installed
                      ? "QuantumShield is installed on this device."
                      : "Install to your home screen / app launcher."}
                  </p>
                  {!installed && (
                    <button
                      onClick={handleInstall}
                      disabled={busy === "install"}
                      className="mt-3 w-full bg-primary text-primary-foreground font-mono text-xs tracking-widest py-2.5 hover:bg-primary/90 transition-all disabled:opacity-50 inline-flex items-center justify-center gap-2"
                      data-testid="button-install"
                    >
                      {busy === "install" ? (
                        <Loader className="w-3.5 h-3.5 animate-spin" />
                      ) : (
                        <Download className="w-3.5 h-3.5" />
                      )}
                      {canPrompt ? "INSTALL APP" : "INSTALL INSTRUCTIONS"}
                    </button>
                  )}
                </div>
              </div>
            </li>

            <li
              className={`border bg-background/40 p-4 ${
                installed ? "border-border/60" : "border-border/30 opacity-60"
              }`}
            >
              <div className="flex items-start gap-3">
                <div
                  className={`w-6 h-6 flex items-center justify-center flex-shrink-0 mt-0.5 ${
                    notifGranted ? "bg-primary/20" : "bg-muted"
                  }`}
                >
                  {notifGranted ? (
                    <CheckCircle className="w-4 h-4 text-primary" />
                  ) : (
                    <Bell className="w-3.5 h-3.5 text-muted-foreground" />
                  )}
                </div>
                <div className="flex-1 min-w-0">
                  <div className="font-mono text-xs font-semibold tracking-widest">
                    STEP 2 · ENABLE PUSH
                  </div>
                  <p className="font-mono text-xs text-muted-foreground mt-1">
                    {notifGranted
                      ? "Encrypted push channel granted."
                      : "Allow encrypted notifications so we can wake the cipher."}
                  </p>
                  {!notifGranted && (
                    <button
                      onClick={handleNotifs}
                      disabled={busy === "notif" || !installed}
                      className="mt-3 w-full bg-primary text-primary-foreground font-mono text-xs tracking-widest py-2.5 hover:bg-primary/90 transition-all disabled:opacity-50 inline-flex items-center justify-center gap-2"
                      data-testid="button-enable-notifications"
                    >
                      {busy === "notif" ? (
                        <Loader className="w-3.5 h-3.5 animate-spin" />
                      ) : (
                        <Bell className="w-3.5 h-3.5" />
                      )}
                      ENABLE PUSH
                    </button>
                  )}
                </div>
              </div>
            </li>
          </ol>

          {error && (
            <div
              className="mt-5 flex items-start gap-2 text-destructive border border-destructive/30 bg-destructive/10 px-3 py-2"
              data-testid="text-gate-error"
            >
              <AlertCircle className="w-4 h-4 flex-shrink-0 mt-0.5" />
              <span className="font-mono text-xs leading-relaxed">{error}</span>
            </div>
          )}
        </div>

        <div className="mt-4 border border-primary/20 bg-primary/5 px-4 py-3 space-y-1">
          <div className="flex items-center gap-2">
            <CheckCircle className="w-3 h-3 text-primary flex-shrink-0" />
            <span className="font-mono text-xs text-muted-foreground">
              Installation creates an offline-capable secure container
            </span>
          </div>
          <div className="flex items-center gap-2">
            <CheckCircle className="w-3 h-3 text-primary flex-shrink-0" />
            <span className="font-mono text-xs text-muted-foreground">
              Push uses VAPID + ECDSA-P256 (end-to-end attestable)
            </span>
          </div>
        </div>
      </div>
    </div>
  );
}
