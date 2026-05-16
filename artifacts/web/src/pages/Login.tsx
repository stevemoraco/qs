import { useState } from "react";
import { Link, useLocation } from "wouter";
import { Shield, AlertCircle } from "lucide-react";
import { usePostAuthLogin } from "@workspace/api-client-react";
import { setToken } from "@/lib/auth";
import { subscribeToPush } from "@/lib/pwa";

export default function Login() {
  const [, setLocation] = useLocation();
  const [username, setUsername] = useState("");
  const [password, setPassword] = useState("");
  const [error, setError] = useState("");

  const login = usePostAuthLogin({
    mutation: {
      onSuccess: (data) => {
        setToken(data.token);
        void subscribeToPush(data.token);
        setLocation("/app");
      },
      onError: () => {
        setError("Invalid username or password");
      },
    },
  });

  const handleSubmit = (e: React.FormEvent) => {
    e.preventDefault();
    setError("");
    login.mutate({ data: { username, password } });
  };

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
            <h1 className="font-mono font-bold text-xl tracking-tight">ACCESS TERMINAL</h1>
            <p className="font-mono text-xs text-muted-foreground mt-2">
              Authenticate to access your encrypted channels
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
                placeholder="username"
                autoComplete="username"
                required
                data-testid="input-username"
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
                placeholder="••••••••"
                autoComplete="current-password"
                required
                data-testid="input-password"
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
              disabled={login.isPending}
              className="w-full bg-primary text-primary-foreground font-mono text-xs tracking-widest py-3 hover:bg-primary/90 transition-all disabled:opacity-50"
              data-testid="button-submit"
            >
              {login.isPending ? "AUTHENTICATING..." : "AUTHENTICATE"}
            </button>
          </form>

          <div className="mt-6 pt-6 border-t border-border/50">
            <p className="font-mono text-xs text-muted-foreground text-center">
              No account?{" "}
              <Link href="/register" className="text-primary hover:underline">
                REQUEST CLEARANCE
              </Link>
            </p>
          </div>
        </div>

        <div className="mt-4 border border-border/30 bg-card/20 px-4 py-3">
          <p className="font-mono text-xs text-muted-foreground text-center">
            <span className="text-primary">// </span>
            Your private keys never leave your device
          </p>
        </div>
      </div>
    </div>
  );
}
