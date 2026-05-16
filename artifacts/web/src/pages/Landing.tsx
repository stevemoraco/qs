import { useEffect, useRef, useState } from "react";
import { Link, Redirect } from "wouter";
import {
  Shield,
  Lock,
  Eye,
  Clock,
  Github,
  Zap,
  Key,
  Cpu,
  ChevronRight,
  Bug,
  ExternalLink,
  Mail,
  UserPlus,
  Users,
  Camera,
  MousePointerClick,
  TimerOff,
  EyeOff,
  MonitorOff,
  Fingerprint,
  UserX,
} from "lucide-react";
import {
  getGetStatsOverviewQueryKey,
  usePostLeads,
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

const PRIVACY_FEATURES = [
  {
    icon: <Camera className="w-5 h-5" />,
    title: "Front-camera recording-device detection",
    desc: "The web client can watch the selfie camera with an on-device object detector for phones, laptops, tablets, cameras, and webcams near the screen. Expo keeps a front-camera sentinel live and reports scan state.",
  },
  {
    icon: <MousePointerClick className="w-5 h-5" />,
    title: "Hold-to-reveal plaintext",
    desc: "Messages stay encrypted in the UI until a deliberate press, tap, or pointer hold. Only one message is revealed at a time, and plaintext clears on release, blur, scroll, or background.",
  },
  {
    icon: <UserX className="w-5 h-5" />,
    title: "Codenamed users and rooms",
    desc: "Usernames, account names, and room names are masked behind per-session codenames until hold-revealed. Shoulder surfers see temporary labels, not your social graph.",
  },
  {
    icon: <TimerOff className="w-5 h-5" />,
    title: "Time-decaying message keys",
    desc: "TTL rooms delete local message keys after expiry. The server can still hold ciphertext, but without the key the content collapses into unrecoverable noise.",
  },
  {
    icon: <EyeOff className="w-5 h-5" />,
    title: "Blur, tab, and app-awareness",
    desc: "Secure content is covered or blurred when the web app loses focus, the tab is hidden, printing starts, or the mobile app backgrounds.",
  },
  {
    icon: <MonitorOff className="w-5 h-5" />,
    title: "Screenshot and print friction",
    desc: "The web client reacts to PrintScreen and print lifecycle events. Expo requests platform screen-capture prevention and warns when screenshot events are reported.",
  },
  {
    icon: <Fingerprint className="w-5 h-5" />,
    title: "Device-local identity keys",
    desc: "Post-quantum identity keys are generated locally during account creation. Private keys are not uploaded to the API.",
  },
  {
    icon: <Key className="w-5 h-5" />,
    title: "Alias and invite codes",
    desc: "Primary alias codes and invite codes control discoverability and access with visibility scopes, max-use limits, allow lists, expirations, and roll/disable controls.",
  },
  {
    icon: <Lock className="w-5 h-5" />,
    title: "Handle plus passkey login",
    desc: "Return access shows only the globally unique handle. Face ID, Touch ID, Windows Hello, or the platform password manager creates and unlocks the passkey.",
  },
  {
    icon: <Shield className="w-5 h-5" />,
    title: "Rotating device sessions",
    desc: "Each successful login issues a fresh bearer session, and logout invalidates only that session while the handle remains rollable or disableable.",
  },
];

const HERO_FEATURES = [
  { icon: <Camera className="w-4 h-4" />, label: "Front-camera recording-device detection" },
  { icon: <MousePointerClick className="w-4 h-4" />, label: "Hold-to-reveal messages that rehide on release" },
  { icon: <TimerOff className="w-4 h-4" />, label: "TTL starts after first view or immediately on send" },
  { icon: <EyeOff className="w-4 h-4" />, label: "Blur, tab, print, and background privacy shield" },
  { icon: <UserX className="w-4 h-4" />, label: "Codenamed users and rooms until deliberate reveal" },
  { icon: <Fingerprint className="w-4 h-4" />, label: "Handle plus passkey access, no typed password field" },
];

const GITHUB_URL = "https://github.com/stevemoraco/qs";
const SECURITY_URL = `${GITHUB_URL}/security`;
const ISSUES_URL = `${GITHUB_URL}/issues`;
const PULLS_URL = `${GITHUB_URL}/pulls`;

type InviteStep = 1 | 2 | 3;

type InviteProfile = {
  email: string;
  name: string;
  phone: string;
  organization: string;
  title: string;
};

const emptyInviteProfile: InviteProfile = {
  email: "",
  name: "",
  phone: "",
  organization: "",
  title: "",
};

export default function Landing() {
  const authenticated = isAuthenticated();
  const { data: stats } = useGetStatsOverview<StatsOverview>({
    query: { queryKey: getGetStatsOverviewQueryKey(), enabled: false },
  });
  const canvasRef = useRef<HTMLCanvasElement>(null);

  useEffect(() => {
    if (authenticated) return;
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
  }, [authenticated]);

  if (authenticated) {
    return <Redirect to="/app" replace />;
  }

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
              <a href="#privacy-stack" className="text-xs font-mono text-muted-foreground hover:text-foreground transition-colors">PRIVACY</a>
              <a href="#ethos" className="text-xs font-mono text-muted-foreground hover:text-foreground transition-colors">ETHOS</a>
              <a href="#security" className="text-xs font-mono text-muted-foreground hover:text-foreground transition-colors">SECURITY</a>
              <a href="#community" className="text-xs font-mono text-muted-foreground hover:text-foreground transition-colors">COMMUNITY</a>
              <a href="#open-source" className="text-xs font-mono text-muted-foreground hover:text-foreground transition-colors">OPEN SOURCE</a>
            </div>
            <Link href="/login"><button className="font-mono text-xs px-4 py-2 border border-border text-muted-foreground hover:text-foreground hover:border-primary/50 transition-all">LOGIN</button></Link>
            <Link href="/register"><button className="font-mono text-xs px-4 py-2 bg-primary text-primary-foreground hover:bg-primary/90 transition-all ml-2">GET ACCESS</button></Link>
          </div>
        </div>
      </nav>

      <section className="relative min-h-screen flex items-center justify-center overflow-hidden">
        <canvas ref={canvasRef} className="absolute inset-0 w-full h-full opacity-30" style={{ pointerEvents: "none" }} />
        <div className="absolute inset-0 bg-[radial-gradient(ellipse_at_center,_var(--tw-gradient-stops))] from-primary/5 via-transparent to-transparent" />
        <div className="relative z-10 text-center max-w-4xl mx-auto px-4 pt-16 md:pt-14">
          <div className="inline-flex items-center gap-2 border border-primary/30 bg-primary/5 px-3 py-1 font-mono text-[10px] text-primary mb-4 backdrop-blur-sm"><span className="w-1.5 h-1.5 bg-primary rounded-full animate-pulse" />NIST FIPS 203 + 204</div>
          <h1 className="font-mono font-bold text-3xl md:text-5xl tracking-tight mb-3 leading-tight">Ask yourself:<br />Why don't "privacy focused" apps work this way?</h1>
          <p className="font-mono text-xs md:text-sm text-muted-foreground max-w-xl mx-auto mb-4 leading-snug">Encrypted. Hold-revealed. Expiring by design.</p>
          <div className="grid grid-cols-1 sm:grid-cols-2 gap-1.5 max-w-2xl mx-auto mb-4 text-left">
            {HERO_FEATURES.map((feature) => (
              <div key={feature.label} className="flex items-center gap-2 border border-border/50 bg-card/35 px-3 py-2 backdrop-blur-sm">
                <span className="text-primary flex-shrink-0">{feature.icon}</span>
                <span className="font-mono text-[11px] text-muted-foreground leading-tight">{feature.label}</span>
              </div>
            ))}
          </div>
          <div className="grid grid-cols-2 gap-2 max-w-xl mx-auto mb-10">
            <Link href="/register"><button className="w-full min-h-14 inline-flex items-center gap-3 bg-primary text-primary-foreground px-4 py-2.5 hover:bg-primary/90 transition-all text-left" data-testid="button-get-access"><UserPlus className="w-4 h-4 flex-shrink-0" /><span><span className="block font-mono text-xs tracking-widest uppercase">Request Clearance</span><span className="block font-mono text-[10px] opacity-80 mt-0.5">Make account</span></span></button></Link>
            <Link href="/login"><button className="w-full min-h-14 inline-flex items-center gap-3 border border-border text-foreground px-4 py-2.5 hover:border-primary/50 transition-all text-left" data-testid="button-login"><Lock className="w-4 h-4 flex-shrink-0" /><span><span className="block font-mono text-xs tracking-widest uppercase">Access Terminal</span><span className="block font-mono text-[10px] text-muted-foreground mt-0.5">Login</span></span></button></Link>
            <a href="#community" className="w-full min-h-14 inline-flex items-center gap-3 border border-primary/40 bg-primary/5 text-primary px-4 py-2.5 hover:border-primary/70 hover:bg-primary/10 transition-all text-left"><Bug className="w-4 h-4 flex-shrink-0" /><span><span className="block font-mono text-xs tracking-widest uppercase">Join Audit</span><span className="block font-mono text-[10px] opacity-80 mt-0.5">Review security</span></span></a>
            <a href={GITHUB_URL} target="_blank" rel="noreferrer" className="w-full min-h-14 inline-flex items-center gap-3 border border-border text-foreground px-4 py-2.5 hover:border-primary/50 transition-all text-left"><Github className="w-4 h-4 flex-shrink-0" /><span><span className="block font-mono text-xs tracking-widest uppercase">GitHub</span><span className="block font-mono text-[10px] text-muted-foreground mt-0.5">View source</span></span></a>
          </div>
          {stats && (
            <div className="grid grid-cols-2 md:grid-cols-4 gap-4 max-w-2xl mx-auto">
              {[
                { label: "USERS", value: stats.totalUsers.toLocaleString() },
                { label: "CHANNELS", value: stats.totalRooms.toLocaleString() },
                { label: "MESSAGES", value: stats.totalMessages.toLocaleString() },
                { label: "ACTIVE TODAY", value: stats.activeRoomsToday.toLocaleString() },
              ].map((s) => <div key={s.label} className="border border-border/50 bg-card/50 p-4 backdrop-blur-sm" data-testid={`stat-${s.label.toLowerCase()}`}><div className="font-mono text-2xl font-bold text-primary">{s.value}</div><div className="font-mono text-xs text-muted-foreground mt-1">{s.label}</div></div>)}
            </div>
          )}
        </div>
      </section>

      <section id="privacy-stack" className="py-24 px-6 border-y border-border/50 bg-background">
        <div className="max-w-7xl mx-auto">
          <div className="max-w-3xl mb-14">
            <div className="font-mono text-xs text-primary tracking-widest mb-3">PRIVACY STACK</div>
            <h2 className="font-mono font-bold text-3xl md:text-5xl leading-tight mb-5">Privacy features most messaging apps never combine.</h2>
            <p className="font-mono text-sm text-muted-foreground leading-relaxed">QuantumShield is built around the moment of exposure: the camera watching the screen, the unfocused tab, the screenshot key, the shoulder glance, and the stale message that should decay into unreadable ciphertext.</p>
          </div>
          <div className="grid grid-cols-1 md:grid-cols-2 xl:grid-cols-3 gap-4">
            {PRIVACY_FEATURES.map((feature) => <div key={feature.title} className="border border-border/50 bg-card/30 p-5"><div className="text-primary mb-4">{feature.icon}</div><h3 className="font-mono text-sm font-semibold mb-3">{feature.title}</h3><p className="font-mono text-xs text-muted-foreground leading-relaxed">{feature.desc}</p></div>)}
          </div>
        </div>
      </section>

      <section id="ethos" className="py-24 px-6 border-y border-border/50 bg-card/20"><div className="max-w-5xl mx-auto"><div className="font-mono text-xs text-primary tracking-widest mb-4">ETHOS / EXPERIMENT</div><h2 className="font-mono font-bold text-3xl md:text-5xl leading-tight mb-8">What is the most secure ideal form of truly ephemeral digital communication?</h2><div className="grid grid-cols-1 lg:grid-cols-[1.2fr_0.8fr] gap-8 items-start"><p className="font-mono text-sm md:text-base text-muted-foreground leading-relaxed">QuantumShield is our working answer to that question. The mission is to build communication software where messages can be encrypted for the quantum era, revealed only with deliberate user intent, and made practically useless after expiry. We are testing whether communities can rely on open, auditable software for private coordination without asking anyone to trust a black box.</p><div className="border border-border/50 bg-background/50 p-6"><p className="font-mono text-xs text-muted-foreground leading-relaxed mb-5">The experiment is public by design: inspect the code, challenge the threat model, report weak assumptions, and help us move closer to dependable ephemeral messaging.</p><div className="flex flex-col sm:flex-row lg:flex-col gap-3"><a href={GITHUB_URL} target="_blank" rel="noreferrer" className="inline-flex items-center justify-center gap-2 border border-border text-foreground font-mono text-xs px-5 py-3 hover:border-primary/50 transition-all tracking-widest uppercase"><Github className="w-4 h-4" />SOURCE</a><a href={SECURITY_URL} target="_blank" rel="noreferrer" className="inline-flex items-center justify-center gap-2 bg-primary text-primary-foreground font-mono text-xs px-5 py-3 hover:bg-primary/90 transition-all tracking-widest uppercase"><Bug className="w-4 h-4" />AUDIT</a></div></div></div></div></section>

      <section id="features" className="py-24 px-6 border-t border-border/50"><div className="max-w-7xl mx-auto"><div className="text-center mb-16"><div className="font-mono text-xs text-primary tracking-widest mb-3">CAPABILITIES</div><h2 className="font-mono font-bold text-3xl md:text-4xl">Security without compromise</h2><p className="font-mono text-sm text-muted-foreground mt-4 max-w-xl mx-auto">Every feature was designed assuming your adversary has a quantum computer.</p></div><div className="grid grid-cols-1 md:grid-cols-2 lg:grid-cols-3 gap-4">{FEATURES.map((f) => <div key={f.title} className="border border-border/50 bg-card/30 p-6 hover:border-primary/30 hover:bg-card/60 transition-all group"><div className="text-primary mb-4 group-hover:scale-110 transition-transform w-fit">{f.icon}</div><h3 className="font-mono font-semibold text-sm tracking-wide mb-3">{f.title}</h3><p className="font-mono text-xs text-muted-foreground leading-relaxed">{f.desc}</p></div>)}</div></div></section>

      <section id="security" className="py-24 px-6 bg-card/20 border-y border-border/50"><div className="max-w-7xl mx-auto"><div className="grid grid-cols-1 lg:grid-cols-2 gap-16 items-center"><div><div className="font-mono text-xs text-primary tracking-widest mb-3">CRYPTOGRAPHIC STACK</div><h2 className="font-mono font-bold text-3xl md:text-4xl mb-6">Every layer verified.<br />Every key quantum-safe.</h2><p className="font-mono text-sm text-muted-foreground mb-8 leading-relaxed">QuantumShield uses only NIST-finalized post-quantum algorithms. No experimental schemes. No proprietary curves. Pure, auditable, open-standard cryptography.</p><p className="font-mono text-sm text-muted-foreground leading-relaxed">When a message expires, the symmetric key is deleted from every device. The ciphertext remains on the server — permanently locked. No court order, no quantum computer, no brute force attack can recover it.</p></div><div className="space-y-2">{ALGORITHMS.map((alg) => <div key={alg.name} className="flex items-center justify-between border border-border/50 bg-card/50 px-5 py-4" data-testid={`algo-${alg.name}`}><div><div className="font-mono font-bold text-sm">{alg.name}</div><div className="font-mono text-xs text-muted-foreground">{alg.spec} — {alg.type}</div></div><div className="flex items-center gap-2"><span className="w-2 h-2 bg-primary rounded-full animate-pulse" /><span className="font-mono text-xs text-primary">{alg.status}</span></div></div>)}<div className="border border-border/50 bg-card/50 px-5 py-4 font-mono text-xs text-muted-foreground leading-relaxed"><span className="text-primary">// </span>Triple-layer: PQ key exchange + PQ signatures + AES-256-GCM. Breaking one layer is mathematically insufficient.</div></div></div></div></section>

      <section className="py-24 px-6 border-t border-border/50"><div className="max-w-7xl mx-auto"><div className="text-center mb-16"><div className="font-mono text-xs text-primary tracking-widest mb-3">THREAT MODEL</div><h2 className="font-mono font-bold text-3xl md:text-4xl">Designed for worst-case adversaries</h2></div><div className="grid grid-cols-1 md:grid-cols-3 gap-4">{[{ threat: "Quantum Computer", defense: "ML-KEM-1024 + ML-DSA-87 resist known quantum attacks including Shor's algorithm." }, { threat: "Physical Observation", defense: "On-device camera detection blanks the screen when a recording device enters the frame." }, { threat: "Screenshot / Screen Recording", defense: "Platform-level screenshot prevention active on all supported devices." }, { threat: "Server Compromise", defense: "End-to-end encrypted. The server sees only ciphertext — never plaintext. Ever." }, { threat: "Retroactive Decryption", defense: "Expired message keys are destroyed. Cryptographically irrecoverable by design." }, { threat: "Supply Chain Attack", defense: "Fully open source. Every dependency is auditable. Run your own server." }].map((t) => <div key={t.threat} className="border border-border/50 bg-card/30 p-6"><div className="flex items-center gap-2 mb-3"><Zap className="w-4 h-4 text-destructive" /><span className="font-mono text-xs font-semibold text-destructive">{t.threat}</span></div><p className="font-mono text-xs text-muted-foreground leading-relaxed">{t.defense}</p></div>)}</div></div></section>

      <section id="open-source" className="py-24 px-6 bg-card/20 border-y border-border/50"><div className="max-w-4xl mx-auto text-center"><div className="font-mono text-xs text-primary tracking-widest mb-3">OPEN SOURCE</div><h2 className="font-mono font-bold text-3xl md:text-4xl mb-6">No black boxes.<br />No trust required.</h2><p className="font-mono text-sm text-muted-foreground mb-10 leading-relaxed max-w-2xl mx-auto">QuantumShield is 100% open source. Audit every cryptographic primitive. Run your own server. Verify that your keys never leave your device. Security through transparency — the only kind that matters.</p><div className="flex flex-col sm:flex-row gap-3 justify-center"><a href={GITHUB_URL} target="_blank" rel="noreferrer" className="inline-flex items-center gap-2 border border-border bg-card text-foreground font-mono text-sm px-8 py-3 hover:border-primary/50 transition-all tracking-widest uppercase"><Github className="w-4 h-4" />VIEW SOURCE</a><a href={SECURITY_URL} target="_blank" rel="noreferrer" className="inline-flex items-center gap-2 border border-border bg-card text-foreground font-mono text-sm px-8 py-3 hover:border-primary/50 transition-all tracking-widest uppercase"><Bug className="w-4 h-4" />SECURITY</a><Link href="/register"><button className="inline-flex items-center gap-2 bg-primary text-primary-foreground font-mono text-sm px-8 py-3 hover:bg-primary/90 transition-all tracking-widest uppercase"><Cpu className="w-4 h-4" />TRY NOW</button></Link></div></div></section>

      <section id="community" className="py-24 px-6 border-y border-border/50"><div className="max-w-7xl mx-auto"><div className="grid grid-cols-1 lg:grid-cols-[1fr_420px] gap-10 items-start"><div><div className="font-mono text-xs text-primary tracking-widest mb-3">CALL FOR REVIEW</div><h2 className="font-mono font-bold text-3xl md:text-4xl mb-6">Auditors, builders, and privacy engineers wanted.</h2><p className="font-mono text-sm text-muted-foreground mb-10 leading-relaxed max-w-2xl">QuantumShield needs independent review, reproducible builds, threat-model pressure, protocol critique, and careful implementation work. If you can break assumptions, harden defaults, document risk, or improve the client experience, start here.</p><div className="grid grid-cols-1 md:grid-cols-3 gap-4">{[{ icon: <Bug className="w-5 h-5" />, title: "Security auditors", copy: "Review auth, crypto boundaries, key storage, API validation, and build provenance.", href: SECURITY_URL, label: "Disclosure" }, { icon: <Users className="w-5 h-5" />, title: "Contributors", copy: "Open focused issues, send small PRs, improve tests, and help keep the workspace maintainable.", href: ISSUES_URL, label: "Issues" }, { icon: <Github className="w-5 h-5" />, title: "Maintainers", copy: "Review pull requests, tighten docs, triage dependency updates, and expand CI coverage.", href: PULLS_URL, label: "Pull requests" }].map((item) => <a key={item.title} href={item.href} target="_blank" rel="noreferrer" className="border border-border/50 bg-card/30 p-5 hover:border-primary/40 hover:bg-card/60 transition-all"><div className="text-primary mb-4">{item.icon}</div><h3 className="font-mono font-semibold text-sm mb-3">{item.title}</h3><p className="font-mono text-xs text-muted-foreground leading-relaxed mb-5">{item.copy}</p><span className="inline-flex items-center gap-2 font-mono text-xs text-primary uppercase tracking-widest">{item.label}<ExternalLink className="w-3 h-3" /></span></a>)}</div></div><MailingListSignup /></div></div></section>

      <footer className="py-10 px-6 border-t border-border/50"><div className="max-w-7xl mx-auto flex flex-col md:flex-row items-center justify-between gap-4"><div className="flex items-center gap-2"><div className="w-5 h-5 bg-primary flex items-center justify-center"><Shield className="w-3 h-3 text-primary-foreground" /></div><span className="font-mono font-bold tracking-widest text-xs">QUANTUMSHIELD</span></div><p className="font-mono text-xs text-muted-foreground">ML-KEM-1024 + ML-DSA-87 + AES-256-GCM — NIST FIPS 203/204/197 Compliant</p></div></footer>
    </div>
  );
}

function MailingListSignup() {
  const [step, setStep] = useState<InviteStep>(1);
  const [profile, setProfile] = useState<InviteProfile>(emptyInviteProfile);
  const [error, setError] = useState("");
  const postLead = usePostLeads();
  const updateProfile = (field: keyof InviteProfile, value: string) => setProfile((current) => ({ ...current, [field]: value }));
  const saveProfile = (nextProfile = profile) => { if (!nextProfile.email) return; localStorage.setItem("qs_invite_profile", JSON.stringify(nextProfile)); };
  const persistLead = async (nextStep: InviteStep, nextProfile = profile) => {
    setError(""); saveProfile(nextProfile);
    try { await postLead.mutateAsync({ data: { email: nextProfile.email, step: nextStep, name: nextProfile.name || null, phone: nextProfile.phone || null, organization: nextProfile.organization || null, title: nextProfile.title || null, source: "homepage" } }); }
    catch { setError("Could not save this step. Please try again."); throw new Error("lead-persist-failed"); }
  };
  const handleEmailSubmit = async (event: React.FormEvent<HTMLFormElement>) => { event.preventDefault(); try { await persistLead(1); setStep(2); } catch {} };
  const handleProfileSubmit = async (event: React.FormEvent<HTMLFormElement>) => { event.preventDefault(); try { await persistLead(2); setStep(3); } catch {} };
  const handleSkipProfile = async () => { try { await persistLead(2); setStep(3); } catch {} };
  const handleCreateAccount = async () => { try { await persistLead(3); window.location.href = createAccountHref; } catch {} };
  const createAccountHref = `/register?email=${encodeURIComponent(profile.email)}&name=${encodeURIComponent(profile.name)}`;
  const isSaving = postLead.isPending;

  return (
    <div className="border border-border/50 bg-card/40 p-6 backdrop-blur-sm">
      <div className="flex items-center gap-2 mb-6"><Mail className="w-5 h-5 text-primary" /><div><h3 className="font-mono font-bold text-lg">Join the project list</h3><p className="font-mono text-xs text-muted-foreground mt-1">Get audit windows, release notes, and contributor calls.</p></div></div>
      <div className="grid grid-cols-3 gap-2 mb-6">{[{ n: 1, label: "Email" }, { n: 2, label: "Profile" }, { n: 3, label: "Account" }].map((s) => <button key={s.n} type="button" onClick={() => { if (s.n === 1 || profile.email) setStep(s.n as InviteStep); }} className={`border px-3 py-2 text-left transition-colors ${step === s.n ? "border-primary bg-primary/10" : "border-border/60 bg-background/40"}`}><span className="font-mono text-[10px] text-muted-foreground block">STEP {s.n}</span><span className="font-mono text-xs text-foreground">{s.label}</span></button>)}</div>
      {step === 1 && <form onSubmit={handleEmailSubmit} className="space-y-4"><div><label className="font-mono text-xs text-muted-foreground block mb-2 tracking-widest">EMAIL</label><input type="email" value={profile.email} onChange={(e) => updateProfile("email", e.target.value)} className="w-full bg-background border border-border px-3 py-2.5 font-mono text-sm text-foreground focus:outline-none focus:border-primary/60 transition-colors" placeholder="you@example.com" autoComplete="email" required /></div><button type="submit" disabled={isSaving} className="w-full bg-primary text-primary-foreground font-mono text-xs tracking-widest py-3 hover:bg-primary/90 transition-all disabled:opacity-50">{isSaving ? "SAVING..." : "CONTINUE"}</button></form>}
      {step === 2 && <form onSubmit={handleProfileSubmit} className="space-y-4"><div className="grid grid-cols-1 sm:grid-cols-2 gap-3"><LabeledInput label="NAME" value={profile.name} onChange={(value) => updateProfile("name", value)} autoComplete="name" placeholder="Optional" /><LabeledInput label="PHONE" value={profile.phone} onChange={(value) => updateProfile("phone", value)} autoComplete="tel" placeholder="Optional" /><LabeledInput label="ORGANIZATION" value={profile.organization} onChange={(value) => updateProfile("organization", value)} autoComplete="organization" placeholder="Optional" /><LabeledInput label="TITLE" value={profile.title} onChange={(value) => updateProfile("title", value)} autoComplete="organization-title" placeholder="Optional" /></div><div className="grid grid-cols-2 gap-3"><button type="button" disabled={isSaving} onClick={handleSkipProfile} className="border border-border text-foreground font-mono text-xs tracking-widest py-3 hover:border-primary/50 transition-all disabled:opacity-50">{isSaving ? "SAVING..." : "SKIP"}</button><button type="submit" disabled={isSaving} className="bg-primary text-primary-foreground font-mono text-xs tracking-widest py-3 hover:bg-primary/90 transition-all disabled:opacity-50">{isSaving ? "SAVING..." : "SAVE PROFILE"}</button></div></form>}
      {step === 3 && <div className="space-y-5"><div className="border border-primary/25 bg-primary/5 p-4"><p className="font-mono text-xs text-muted-foreground leading-relaxed">{profile.email} is queued for project updates in this browser. Create a secure account next to generate your post-quantum identity keys locally.</p></div><div className="flex flex-col gap-3"><button onClick={handleCreateAccount} disabled={isSaving} className="w-full inline-flex items-center justify-center gap-2 bg-primary text-primary-foreground font-mono text-xs tracking-widest py-3 hover:bg-primary/90 transition-all disabled:opacity-50"><UserPlus className="w-4 h-4" />{isSaving ? "SAVING..." : "CREATE ACCOUNT"}</button><a href={GITHUB_URL} target="_blank" rel="noreferrer" className="w-full inline-flex items-center justify-center gap-2 border border-border text-foreground font-mono text-xs tracking-widest py-3 hover:border-primary/50 transition-all"><Github className="w-4 h-4" />REVIEW SOURCE FIRST</a></div></div>}
      {error && <p className="font-mono text-xs text-destructive mt-4" role="alert">{error}</p>}
    </div>
  );
}

function LabeledInput({ label, value, onChange, autoComplete, placeholder }: { label: string; value: string; onChange: (value: string) => void; autoComplete: string; placeholder: string; }) {
  return <div><label className="font-mono text-xs text-muted-foreground block mb-2 tracking-widest">{label}</label><input type="text" value={value} onChange={(e) => onChange(e.target.value)} className="w-full bg-background border border-border px-3 py-2.5 font-mono text-sm text-foreground focus:outline-none focus:border-primary/60 transition-colors" placeholder={placeholder} autoComplete={autoComplete} /></div>;
}
