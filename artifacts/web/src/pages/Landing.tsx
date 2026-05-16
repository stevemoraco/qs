import { useEffect, useRef } from "react";
import { Link } from "wouter";
import { Shield, Lock, Eye, Clock, Github, Zap, Key, Cpu, ChevronRight } from "lucide-react";
import {
  getGetStatsOverviewQueryKey,
  useGetStatsOverview,
  type StatsOverview,
} from "@workspace/api-client-react";
import { isAuthenticated } from "@/lib/auth";

const FEATURES = [
  {
    icon: <Key className="w-6 h-6" />,
    title: "ML-KEM-1024 Key Exchange",
    desc: "NIST FIPS 203 finalized standard. Quantum-safe key encapsulation that cannot be broken by Shor's algorithm — not in 2024, not in 2124.",
  },
  {
    icon: <Shield className="w-6 h-6" />,
    title: "ML-DSA-87 Message Signing",
    desc: "NIST FIPS 204 digital signatures. Every message is cryptographically signed at the hardware level. Tampering is mathematically impossible.",
  },
  {
    icon: <Lock className="w-6 h-6" />,
    title: "AES-256-GCM Symmetric Layer",
    desc: "256-bit symmetric encryption for every message payload. The triple layer — PQ KEM + PQ DSA + AES-GCM — means breaking one cipher breaks nothing.",
  },
  {
    icon: <Eye className="w-6 h-6" />,
    title: "On-Device Camera Detection",
    desc: "An on-device ML model monitors your selfie camera at all times. If a recording device is detected in frame, the screen instantly blanks and you're warned.",
  },
  {
    icon: <Clock className="w-6 h-6" />,
    title: "Cryptographic Message Expiry",
    desc: "Set a TTL. When it expires, the symmetric key is destroyed client-side. The ciphertext remains on the server — permanently unreadable. No key, no message.",
  },
  {
    icon: <Github className="w-6 h-6" />,
    title: "Fully Open Source",
    desc: "Every line of code is public. No black boxes. No proprietary algorithms. Audit it, fork it, run it yourself. Security through transparency, not obscurity.",
  },
];

const ALGORITHMS = [
  { name: "ML-KEM-1024", spec: "NIST FIPS 203", type: "Key Exchange", status: "Active" },
  { name: "ML-DSA-87", spec: "NIST FIPS 204", type: "Signatures", status: "Active" },
  { name: "AES-256-GCM", spec: "NIST FIPS 197", type: "Symmetric", status: "Active" },
  { name: "Argon2id", spec: "RFC 9106", type: "Key Derivation", status: "Active" },
];

export default function Landing() {
  const { data: stats } = useGetStatsOverview<StatsOverview>({
    query: { queryKey: getGetStatsOverviewQueryKey(), enabled: isAuthenticated() },
  });
  const canvasRef = useRef<HTMLCanvasElement>(null);

  useEffect(() => {
    const canvas = canvasRef.current;
    if (!canvas) return;
    const ctx = canvas.getContext("2d");
    if (!ctx) return;

    canvas.width = canvas.offsetWidth;
    canvas.height = canvas.offsetHeight;

    const chars = "01ABCDEF∑∆∇∈∉⊕⊗⊥∥∀∃ML-KEM";
    const cols = Math.floor(canvas.width / 14);
    const drops: number[] = Array(cols).fill(1);

    const draw = () => {
      ctx.fillStyle = "rgba(6, 8, 14, 0.05)";
      ctx.fillRect(0, 0, canvas.width, canvas.height);
      ctx.fillStyle = "#06b6d466";
      ctx.font = "12px monospace";
      for (let i = 0; i < drops.length; i++) {
        const text = chars[Math.floor(Math.random() * chars.length)];
        ctx.fillText(text, i * 14, drops[i] * 14);
        if (drops[i] * 14 > canvas.height && Math.random() > 0.975) drops[i] = 0;
        drops[i]++;
      }
    };

    const interval = setInterval(draw, 50);
    return () => clearInterval(interval);
  }, []);

  return (
    <div className="min-h-screen bg-background text-foreground overflow-x-hidden">
      <nav className="fixed top-0 left-0 right-0 z-50 border-b border-border/50 bg-background/80 backdrop-blur-md">
        <div className="max-w-7xl mx-auto px-6 h-14 flex items-center justify-between">
          <div className="flex items-center gap-2">
            <div className="w-6 h-6 bg-primary flex items-center justify-center">
              <Shield className="w-3.5 h-3.5 text-primary-foreground" />
            </div>
            <span className="font-mono font-bold tracking-widest text-sm">QUANTUMSHIELD</span>
          </div>
          <div className="flex items-center gap-1">
            <div className="hidden md:flex items-center gap-4 mr-6">
              <a href="#features" className="text-xs font-mono text-muted-foreground hover:text-foreground transition-colors">FEATURES</a>
              <a href="#security" className="text-xs font-mono text-muted-foreground hover:text-foreground transition-colors">SECURITY</a>
              <a href="#open-source" className="text-xs font-mono text-muted-foreground hover:text-foreground transition-colors">OPEN SOURCE</a>
            </div>
            <Link href="/login">
              <button className="font-mono text-xs px-4 py-2 border border-border text-muted-foreground hover:text-foreground hover:border-primary/50 transition-all">
                LOGIN
              </button>
            </Link>
            <Link href="/register">
              <button className="font-mono text-xs px-4 py-2 bg-primary text-primary-foreground hover:bg-primary/90 transition-all ml-2">
                GET ACCESS
              </button>
            </Link>
          </div>
        </div>
      </nav>

      <section className="relative min-h-screen flex items-center justify-center overflow-hidden">
        <canvas
          ref={canvasRef}
          className="absolute inset-0 w-full h-full opacity-30"
          style={{ pointerEvents: "none" }}
        />
        <div className="absolute inset-0 bg-[radial-gradient(ellipse_at_center,_var(--tw-gradient-stops))] from-primary/5 via-transparent to-transparent" />

        <div className="relative z-10 text-center max-w-5xl mx-auto px-6 pt-14">
          <div className="inline-flex items-center gap-2 border border-primary/30 bg-primary/5 px-3 py-1.5 font-mono text-xs text-primary mb-10 backdrop-blur-sm">
            <span className="w-1.5 h-1.5 bg-primary rounded-full animate-pulse" />
            NIST FIPS 203 + 204 COMPLIANT — POST-QUANTUM SECURE
          </div>

          <h1 className="font-mono font-bold text-6xl md:text-8xl tracking-tighter mb-6 leading-none">
            QUANTUM
            <br />
            <span className="text-primary">SHIELD</span>
          </h1>

          <p className="font-mono text-sm md:text-base text-muted-foreground max-w-2xl mx-auto mb-12 leading-relaxed">
            The only messaging platform that encrypts for the quantum era.
            <br />
            ML-KEM-1024 key exchange. ML-DSA-87 signatures. Zero compromise.
          </p>

          <div className="flex flex-col sm:flex-row gap-3 justify-center mb-20">
            <Link href="/register">
              <button className="inline-flex items-center gap-2 bg-primary text-primary-foreground font-mono text-sm px-8 py-3 hover:bg-primary/90 transition-all tracking-widest uppercase" data-testid="button-get-access">
                REQUEST CLEARANCE
                <ChevronRight className="w-4 h-4" />
              </button>
            </Link>
            <Link href="/login">
              <button className="inline-flex items-center gap-2 border border-border text-foreground font-mono text-sm px-8 py-3 hover:border-primary/50 transition-all tracking-widest uppercase" data-testid="button-login">
                ACCESS TERMINAL
              </button>
            </Link>
          </div>

          {stats && (
            <div className="grid grid-cols-2 md:grid-cols-4 gap-4 max-w-2xl mx-auto">
              {[
                { label: "USERS", value: stats.totalUsers.toLocaleString() },
                { label: "CHANNELS", value: stats.totalRooms.toLocaleString() },
                { label: "MESSAGES", value: stats.totalMessages.toLocaleString() },
                { label: "ACTIVE TODAY", value: stats.activeRoomsToday.toLocaleString() },
              ].map((s) => (
                <div key={s.label} className="border border-border/50 bg-card/50 p-4 backdrop-blur-sm" data-testid={`stat-${s.label.toLowerCase()}`}>
                  <div className="font-mono text-2xl font-bold text-primary">{s.value}</div>
                  <div className="font-mono text-xs text-muted-foreground mt-1">{s.label}</div>
                </div>
              ))}
            </div>
          )}
        </div>
      </section>

      <section id="features" className="py-24 px-6 border-t border-border/50">
        <div className="max-w-7xl mx-auto">
          <div className="text-center mb-16">
            <div className="font-mono text-xs text-primary tracking-widest mb-3">CAPABILITIES</div>
            <h2 className="font-mono font-bold text-3xl md:text-4xl">Security without compromise</h2>
            <p className="font-mono text-sm text-muted-foreground mt-4 max-w-xl mx-auto">
              Every feature was designed assuming your adversary has a quantum computer.
            </p>
          </div>

          <div className="grid grid-cols-1 md:grid-cols-2 lg:grid-cols-3 gap-4">
            {FEATURES.map((f) => (
              <div key={f.title} className="border border-border/50 bg-card/30 p-6 hover:border-primary/30 hover:bg-card/60 transition-all group">
                <div className="text-primary mb-4 group-hover:scale-110 transition-transform w-fit">
                  {f.icon}
                </div>
                <h3 className="font-mono font-semibold text-sm tracking-wide mb-3">{f.title}</h3>
                <p className="font-mono text-xs text-muted-foreground leading-relaxed">{f.desc}</p>
              </div>
            ))}
          </div>
        </div>
      </section>

      <section id="security" className="py-24 px-6 bg-card/20 border-y border-border/50">
        <div className="max-w-7xl mx-auto">
          <div className="grid grid-cols-1 lg:grid-cols-2 gap-16 items-center">
            <div>
              <div className="font-mono text-xs text-primary tracking-widest mb-3">CRYPTOGRAPHIC STACK</div>
              <h2 className="font-mono font-bold text-3xl md:text-4xl mb-6">
                Every layer verified.
                <br />
                Every key quantum-safe.
              </h2>
              <p className="font-mono text-sm text-muted-foreground mb-8 leading-relaxed">
                QuantumShield uses only NIST-finalized post-quantum algorithms. No experimental
                schemes. No proprietary curves. Pure, auditable, open-standard cryptography.
              </p>
              <p className="font-mono text-sm text-muted-foreground leading-relaxed">
                When a message expires, the symmetric key is deleted from every device. 
                The ciphertext remains on the server — permanently locked. 
                No court order, no quantum computer, no brute force attack can recover it.
              </p>
            </div>
            <div className="space-y-2">
              {ALGORITHMS.map((alg) => (
                <div key={alg.name} className="flex items-center justify-between border border-border/50 bg-card/50 px-5 py-4" data-testid={`algo-${alg.name}`}>
                  <div>
                    <div className="font-mono font-bold text-sm">{alg.name}</div>
                    <div className="font-mono text-xs text-muted-foreground">{alg.spec} — {alg.type}</div>
                  </div>
                  <div className="flex items-center gap-2">
                    <span className="w-2 h-2 bg-primary rounded-full animate-pulse" />
                    <span className="font-mono text-xs text-primary">{alg.status}</span>
                  </div>
                </div>
              ))}
              <div className="border border-border/50 bg-card/50 px-5 py-4 font-mono text-xs text-muted-foreground leading-relaxed">
                <span className="text-primary">// </span>
                Triple-layer: PQ key exchange + PQ signatures + AES-256-GCM.
                Breaking one layer is mathematically insufficient.
              </div>
            </div>
          </div>
        </div>
      </section>

      <section className="py-24 px-6 border-t border-border/50">
        <div className="max-w-7xl mx-auto">
          <div className="text-center mb-16">
            <div className="font-mono text-xs text-primary tracking-widest mb-3">THREAT MODEL</div>
            <h2 className="font-mono font-bold text-3xl md:text-4xl">Designed for worst-case adversaries</h2>
          </div>
          <div className="grid grid-cols-1 md:grid-cols-3 gap-4">
            {[
              { threat: "Quantum Computer", defense: "ML-KEM-1024 + ML-DSA-87 resist known quantum attacks including Shor's algorithm." },
              { threat: "Physical Observation", defense: "On-device camera detection blanks the screen when a recording device enters the frame." },
              { threat: "Screenshot / Screen Recording", defense: "Platform-level screenshot prevention active on all supported devices." },
              { threat: "Server Compromise", defense: "End-to-end encrypted. The server sees only ciphertext — never plaintext. Ever." },
              { threat: "Retroactive Decryption", defense: "Expired message keys are destroyed. Cryptographically irrecoverable by design." },
              { threat: "Supply Chain Attack", defense: "Fully open source. Every dependency is auditable. Run your own server." },
            ].map((t) => (
              <div key={t.threat} className="border border-border/50 bg-card/30 p-6">
                <div className="flex items-center gap-2 mb-3">
                  <Zap className="w-4 h-4 text-destructive" />
                  <span className="font-mono text-xs font-semibold text-destructive">{t.threat}</span>
                </div>
                <p className="font-mono text-xs text-muted-foreground leading-relaxed">{t.defense}</p>
              </div>
            ))}
          </div>
        </div>
      </section>

      <section id="open-source" className="py-24 px-6 bg-card/20 border-y border-border/50">
        <div className="max-w-4xl mx-auto text-center">
          <div className="font-mono text-xs text-primary tracking-widest mb-3">OPEN SOURCE</div>
          <h2 className="font-mono font-bold text-3xl md:text-4xl mb-6">
            No black boxes.
            <br />
            No trust required.
          </h2>
          <p className="font-mono text-sm text-muted-foreground mb-10 leading-relaxed max-w-2xl mx-auto">
            QuantumShield is 100% open source. Audit every cryptographic primitive. 
            Run your own server. Verify that your keys never leave your device. 
            Security through transparency — the only kind that matters.
          </p>
          <div className="flex flex-col sm:flex-row gap-3 justify-center">
            <a href="https://github.com" className="inline-flex items-center gap-2 border border-border bg-card text-foreground font-mono text-sm px-8 py-3 hover:border-primary/50 transition-all tracking-widest uppercase">
              <Github className="w-4 h-4" />
              VIEW SOURCE
            </a>
            <Link href="/register">
              <button className="inline-flex items-center gap-2 bg-primary text-primary-foreground font-mono text-sm px-8 py-3 hover:bg-primary/90 transition-all tracking-widest uppercase">
                <Cpu className="w-4 h-4" />
                TRY NOW
              </button>
            </Link>
          </div>
        </div>
      </section>

      <footer className="py-10 px-6 border-t border-border/50">
        <div className="max-w-7xl mx-auto flex flex-col md:flex-row items-center justify-between gap-4">
          <div className="flex items-center gap-2">
            <div className="w-5 h-5 bg-primary flex items-center justify-center">
              <Shield className="w-3 h-3 text-primary-foreground" />
            </div>
            <span className="font-mono font-bold tracking-widest text-xs">QUANTUMSHIELD</span>
          </div>
          <p className="font-mono text-xs text-muted-foreground">
            ML-KEM-1024 + ML-DSA-87 + AES-256-GCM — NIST FIPS 203/204/197 Compliant
          </p>
        </div>
      </footer>
    </div>
  );
}
