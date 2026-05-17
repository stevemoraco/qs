import { Fragment, useEffect, useRef, useState } from "react";
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
  Globe,
  Server,
  ScanFace,
  AlertTriangle,
  HardDrive,
  FolderSearch,
  Database,
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
    desc: "Set a TTL. When it expires, clients purge local keys and the API wipes wrapped key envelopes. Ciphertext can remain, but there is no usable key path left. No key, no message.",
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
    desc: "TTL rooms purge local message keys and server-side wrapped key envelopes after expiry. The server can still hold ciphertext, but without a usable key path the content collapses into unrecoverable noise.",
  },
  {
    icon: <EyeOff className="w-5 h-5" />,
    title: "Blur, tab, and app-awareness",
    desc: "Secure content is covered or blurred when the web app loses focus, the tab is hidden, printing starts, or the mobile app backgrounds.",
  },
  {
    icon: <MonitorOff className="w-5 h-5" />,
    title: "Capture guard notifications",
    desc: "The PWA warns and locks when browsers expose capture-adjacent events like PrintScreen, print/save-to-PDF, clipboard copy, blur, or app backgrounding. Native screenshot blocking requires platform APIs outside Safari/Chrome PWAs.",
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
  { icon: <Camera className="w-4 h-4" />, label: "Selfie camera sees another device or screenshot flash, locks chat + warns them" },
  { icon: <MousePointerClick className="w-4 h-4" />, label: "Hold-to-reveal messages that rehide on release" },
  { icon: <TimerOff className="w-4 h-4" />, label: "TTL starts after first view or immediately on send" },
  { icon: <EyeOff className="w-4 h-4" />, label: "Blur, tab, print, and background privacy shield" },
  { icon: <UserX className="w-4 h-4" />, label: "Codenamed users and rooms until deliberate reveal" },
  { icon: <Fingerprint className="w-4 h-4" />, label: "Handle plus passkey access, no typed password field" },
];

const CRYPTO_ROLES = [
  {
    icon: <Key className="w-5 h-5" />,
    name: "ML-KEM-1024",
    expanded: "Module-Lattice-Based Key Encapsulation Mechanism",
    role: "Wraps each fresh message key to each recipient device using post-quantum lattice math.",
  },
  {
    icon: <Shield className="w-5 h-5" />,
    name: "ML-DSA-87",
    expanded: "Module-Lattice-Based Digital Signature Algorithm",
    role: "Signs message packages and key bundles so tampering is rejected before plaintext can exist.",
  },
  {
    icon: <Lock className="w-5 h-5" />,
    name: "AES-256-GCM",
    expanded: "Advanced Encryption Standard, 256-bit key, Galois Counter Mode",
    role: "Encrypts the message body itself with authenticated symmetric encryption.",
  },
  {
    icon: <Fingerprint className="w-5 h-5" />,
    name: "Argon2id",
    expanded: "Argon2 identity-hybrid password hashing mode",
    role: "Hardens account secrets against guessing. It protects auth, not the message payload.",
  },
];

const DISTRIBUTION_DEFENSES = [
  {
    icon: <Globe className="w-5 h-5" />,
    title: "No App Store gate",
    copy: "The PWA ships instantly from the open repo. Auditors can inspect, fork, self-host, and verify behavior without waiting for store review.",
  },
  {
    icon: <Fingerprint className="w-5 h-5" />,
    title: "Platform passkeys",
    copy: "Login uses the browser platform authenticator, so supported devices route account access through Face ID, Touch ID, Windows Hello, device passcode, and secure hardware-backed key storage.",
  },
  {
    icon: <MousePointerClick className="w-5 h-5" />,
    title: "Plaintext by intent only",
    copy: "Encrypted messages do not render as plaintext until a deliberate hold or tap. Release, blur, scroll, or backgrounding clears the reveal.",
  },
  {
    icon: <ScanFace className="w-5 h-5" />,
    title: "Physical capture awareness",
    copy: "Camera-based local checks look for another recording device or screen-flash reflection while sensitive content is revealed.",
  },
  {
    icon: <MonitorOff className="w-5 h-5" />,
    title: "Browser-exposed capture events",
    copy: "Print, clipboard, visibility, focus, and screenshot-key-adjacent events lock the privacy shield where browsers expose those signals.",
  },
  {
    icon: <Server className="w-5 h-5" />,
    title: "Server sees ciphertext",
    copy: "The API stores encrypted message packages and wrapped keys. Message plaintext and private post-quantum identity keys stay client-side.",
  },
];

const PROTOCOL_COMPARISON = [
  {
    stage: "Account identity",
    icon: <Fingerprint className="w-5 h-5" />,
    quantumShieldLead: "We store a peppered lookup value, not your handle.",
    signalLead: "Signal can store a username record even when you hide your phone number.",
    imessageLead: "your Apple account, phone number, and devices are part of the map.",
    quantumShield: "You type a handle locally, then Face ID, Touch ID, Windows Hello, or your passkey provider proves it is really you. The app sends a deterministic handle hash over TLS; the server applies its own secret pepper and stores only that server-side lookup value. We do not receive your readable handle, face, fingerprint, device passcode, typed password, or passkey private key.",
    signal: "You start with a phone number. A username can let new people contact you without seeing that number, but the username still exists as a service-managed account identifier. Signal's PIN/Secure Value Recovery helps restore profile, contacts, and groups privately.",
    imessage: "You sign in with Apple ID and reachable phone numbers or email addresses. Apple coordinates which devices can receive your iMessages.",
    warning: "What this means: your exact handle can be found by someone who already knows and types it, but the database does not need the readable handle for lookup. A powerful adversary still cares about sessions, devices, room joins, timing, and push routes.",
  },
  {
    stage: "Initial key establishment",
    icon: <Key className="w-5 h-5" />,
    quantumShieldLead: "Every message gets its own key, fuzzed timing, and optional time-decay protection.",
    signalLead: "a powerful attacker can still study who started talking and when.",
    imessageLead: "Apple helps decide which devices get each message.",
    quantumShield: "When you send a message, the app gives it a fresh key and can blur the exact send time with random delivery fuzz. Experimental decay rooms are designed so encryption weakens automatically as real time passes, using multiple time checks instead of trusting one device clock or one server clock. The server carries the package but is mathematically guaranteed not to have the key needed to read it; check the source code and verify the key path.",
    signal: "When a Signal chat starts, PQXDH mixes classical X25519 with post-quantum Kyber-derived secret material. The goal is to make today's captured setup traffic useless to a future quantum computer.",
    imessage: "When supported Apple devices talk, PQ3 adds post-quantum key material to iMessage setup so recorded traffic is harder to decrypt later.",
    warning: "What this means: the first handshake is where future decryption risk begins. If an attacker records everything today, post-quantum setup is what keeps those recordings from becoming readable when quantum attacks improve.",
  },
  {
    stage: "Ongoing conversation security",
    icon: <Shield className="w-5 h-5" />,
    quantumShieldLead: "Tampering is rejected before plaintext exists.",
    signalLead: "you still trust the app and device to show the real conversation.",
    imessageLead: "you cannot easily see or audit every protection step yourself.",
    quantumShield: "Before your device decrypts, it verifies the message package with ML-DSA-87. If the ciphertext, wrapped keys, room, sender, or algorithm fields were changed, the message is rejected instead of shown.",
    signal: "Signal continuously ratchets keys as the chat continues, so compromise at one moment does not automatically reveal every past and future message.",
    imessage: "Apple describes PQ3 as protecting both the setup and the ongoing conversation, with rekeying as messages continue between supported devices.",
    warning: "What this means: encryption answers 'can they read it?' Signatures and verification answer 'can they fake or alter it?' A serious attacker tries both.",
  },
  {
    stage: "Metadata and routing",
    icon: <Server className="w-5 h-5" />,
    quantumShieldLead: "We say exactly what metadata still exists.",
    signalLead: "even hidden messages can leave clues about your activity.",
    imessageLead: "Apple routing can show which account and devices were involved.",
    quantumShield: "Our server sees operational records: ciphertext, room membership, wrapped keys, delivery state, sessions, peppered handle lookup values, and push tokens. That is why the product calls out metadata as an audit target.",
    signal: "Signal works hard to reduce server-visible metadata, including private contact and group recovery designs, but some timing, network, registration, and delivery facts can still exist around the system.",
    imessage: "Apple infrastructure handles account lookup, device lookup, delivery, push, sync choices, and account/device coordination for iMessage.",
    warning: "What this means: even unreadable messages can leave a pattern. A nation-state with carrier logs, internet routing visibility, push logs, device records, or server history can study who was active, when, from where, and with which devices.",
  },
  {
    stage: "Plaintext exposure on screen",
    icon: <EyeOff className="w-5 h-5" />,
    quantumShieldLead: "Plaintext only appears while you deliberately reveal it.",
    signalLead: "once a message is on screen, malware or a camera can copy it.",
    imessageLead: "previews, screenshots, and backups can expose what encryption protected.",
    quantumShield: "You hold to reveal one message at a time. Let go, switch tabs, scroll, background the app, trigger capture warnings, or point another camera at the screen and the chat hides again.",
    signal: "Signal can protect local use with app lock, screen security, disappearing messages, and notification privacy where the operating system supports it.",
    imessage: "iMessage relies on Apple device protections like lock screen settings, notification privacy, Focus, and device-level screenshot/backup behavior.",
    warning: "What this means: the screen is often the weakest moment. A second phone, malware, a screenshot, a backup, or a notification preview can expose content after perfect encryption already did its job.",
  },
  {
    stage: "Time decay and deletion",
    icon: <TimerOff className="w-5 h-5" />,
    quantumShieldLead: "Experimental decay is designed to follow real time, not fake clocks.",
    signalLead: "disappearing later does not erase what someone already copied.",
    imessageLead: "deleting in one place may not delete every synced or backed-up copy.",
    quantumShield: "You choose whether the timer starts when a message is first viewed or immediately when sent. In standard decay, clients purge local message keys and the API wipes wrapped key envelopes after expiry. Experimental decay is designed to be Sybil-resistant: rolling back your phone clock or faking one server clock should not bring an expired message back, because time must be backed by multiple independent checks. Leftover server ciphertext is mathematically guaranteed to be unreadable noise without a usable key path. Check the source code and verify the timed key purge.",
    signal: "Signal disappearing messages remove messages after a timer, but recipients or compromised devices may already have copied or captured them.",
    imessage: "iMessage deletion depends on the sender's devices, recipient devices, sync state, retention settings, and backups.",
    warning: "What this means: deletion only helps before collection. If someone already saw it, photographed it, backed it up, or compromised the endpoint, a later timer cannot make that copy disappear.",
  },
];

const PROTOCOL_REFERENCES = [
  { label: "Apple PQ3", href: "https://security.apple.com/blog/imessage-pq3/" },
  { label: "Signal PQXDH", href: "https://signal.org/blog/pqxdh/" },
  { label: "Signal post-quantum ratchet", href: "https://signal.org/blog/spqr/" },
  { label: "Signal usernames", href: "https://support.signal.org/hc/en-us/articles/6712070553754-Phone-Number-Privacy-and-Usernames" },
  { label: "Signal PIN/SVR", href: "https://support.signal.org/hc/en-us/articles/360007059792-Signal-PIN" },
];

const LOCAL_DEVICE_EXPOSURE = [
  {
    name: "QuantumShield",
    tone: "benefit",
    icon: <MousePointerClick className="w-5 h-5" />,
    plain: "With QuantumShield, they need your face or fingerprint to read each message.",
    headline: "Every reveal is deliberate, one message at a time, and passkey-gated on supported devices.",
    runningPlain: "Even if someone gets your device, they still have to pass the biometric check for each message reveal.",
    running: [
      "RAM can contain decrypted plaintext only for the message currently being held or intentionally revealed.",
      "RAM can contain active session state and local decryption keys while the app is unlocked.",
      "Release, blur, background, scroll, privacy shield, or capture detection clears visible plaintext.",
      "The design keeps usable reveal behind passkey-gated device authentication, even against malware or an AI agent using the device.",
    ],
    stoppedPlain: "If someone copies local files, steals local keys, or uploads device data, they get encrypted packages instead of a readable chat history.",
    stopped: [
      "Disk is intended to hold ciphertext packages, wrapped keys, public key material, and app/session metadata.",
      "Readable handles stay local; the server stores peppered exact-lookup values instead of readable handles.",
      "Expired local message keys and server-side wrapped key envelopes are removed so old ciphertext is mathematically guaranteed to remain unreadable.",
      "A quantum computer that breaks classical encryption still does not turn expired ciphertext into readable messages without the destroyed usable key.",
    ],
    implicationPlain: "A bad actor has to beat your Face ID, Touch ID, or device biometric check for the one message being revealed.",
    implication: "QuantumShield is designed so local keys are protected by passkey-gated device authentication, plaintext appears only for the message currently being held or intentionally revealed, and normal chat history is mathematically guaranteed not to sit on disk or remain broadly readable in memory where a bad actor could silently copy or upload it. Check the source code and verify the storage and reveal paths.",
  },
  {
    name: "Signal",
    tone: "risk",
    icon: <Database className="w-5 h-5" />,
    plain: "With Signal, a bad actor can go after the chat history saved on your device.",
    headline: "Desktop and phone history, attachments, and notifications can become local app targets.",
    runningPlain: "While Signal is open, your device can already see your chats.",
    running: [
      "RAM can contain the messages, contacts, attachments, previews, and keys the desktop app or phone app is actively using.",
      "The app must decrypt content locally to render conversations and attachments.",
      "Screen security/app lock reduce casual exposure but do not hide content from malware already running as you on a computer or phone.",
    ],
    stoppedPlain: "When Signal is closed, local chat records can still be a target.",
    stopped: [
      "Disk or device storage can contain Signal's local encrypted database, attachment files/state, preferences, and key material needed by the client.",
      "The database is not a simple plaintext file, but the app must retain enough local material to reopen your history.",
      "OS account compromise, phone compromise, backups, screenshots, exports, and notification artifacts can still matter.",
    ],
    implicationPlain: "If they get into your unlocked device, they can try to grab your chats, files, contacts, and alerts.",
    implication: "A local AI agent or malware with your user privileges may not need to break Signal's network encryption; it can target the app's local dataset, live process, screen, clipboard, notifications, or backups on a computer or phone.",
  },
  {
    name: "iMessage",
    tone: "risk",
    icon: <FolderSearch className="w-5 h-5" />,
    plain: "With iMessage, your Apple device can keep years of messages ready to search.",
    headline: "Mac and iPhone message history, attachments, contacts, and alerts are ordinary local targets.",
    runningPlain: "While iMessage is open, your device can show your messages, files, previews, and alerts.",
    running: [
      "RAM can contain open conversations, rendered plaintext, attachments, notification state, and account/device sync state.",
      "The Messages app and system services can render searchable conversation history on your unlocked Mac or phone.",
      "Anything visible to the user can also be visible to screen-reading malware, phone malware, screenshots, remote control tools, or a local agent.",
    ],
    stoppedPlain: "When iMessage is closed, old messages and photos can still live on your device.",
    stopped: [
      "Mac disk commonly contains Messages history under the user Library Messages database and attachment folders; phones can also retain local message databases, attachments, notifications, and backup-derived copies.",
      "Local storage may also expose contacts, handles, previews, Spotlight/search artifacts, caches, and backup-derived copies depending on settings.",
      "iCloud settings, local retention, backups, FileVault, device lock state, and Advanced Data Protection change the exposure.",
    ],
    implicationPlain: "If they get into your unlocked Apple device, they can target years of messages, photos, contacts, and previews.",
    implication: "A local AI agent, malware process, remote admin tool, phone malware, or person with access to your unlocked Apple device can often inspect the endpoint record directly. If plaintext exists on disk or in local app stores, a bad actor can silently copy or upload it without breaking transport encryption.",
  },
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
              <a href="#security-model" className="text-xs font-mono text-muted-foreground hover:text-foreground transition-colors">MODEL</a>
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
        <div className="relative z-10 text-center max-w-4xl mx-auto px-4 pt-8 md:pt-7">
          <div className="inline-flex items-center gap-2 border border-primary/30 bg-primary/5 px-3 py-1 font-mono text-[10px] text-primary mb-4 backdrop-blur-sm"><span className="w-1.5 h-1.5 bg-primary rounded-full animate-pulse" />ML-KEM-1024 + ML-DSA-87 + AES-256-GCM - NIST FIPS 203/204/197</div>
          <h1 className="font-mono font-bold text-3xl md:text-5xl tracking-tight mb-3 leading-tight">
            Ask yourself:
            <span className="block mx-auto mt-1 max-w-3xl text-primary italic text-2xl md:text-4xl leading-tight">
              Why don't "privacy focused" apps <span className="whitespace-nowrap">work this way?</span>
            </span>
          </h1>
          <p className="font-mono text-xs md:text-sm text-muted-foreground max-w-xl mx-auto mb-4 leading-snug">PQ encrypted. Hold-revealed. Self-expiring.</p>
          <div className="grid grid-cols-1 sm:grid-cols-2 gap-1.5 max-w-2xl mx-auto mb-4 text-left">
            {HERO_FEATURES.map((feature) => (
              <div key={feature.label} className="flex items-center gap-2 border border-border/50 bg-card/35 px-3 py-2 backdrop-blur-sm">
                <span className="text-primary flex-shrink-0">{feature.icon}</span>
                <span className="font-mono text-[11px] text-muted-foreground leading-tight">{feature.label}</span>
              </div>
            ))}
          </div>
          <div className="grid grid-cols-2 gap-2 max-w-xl mx-auto mb-10">
            <Link href="/register"><button className="w-full min-h-14 inline-flex items-center gap-2 bg-primary text-primary-foreground px-3 py-2.5 hover:bg-primary/90 transition-all text-left" data-testid="button-get-access"><UserPlus className="w-4 h-4 flex-shrink-0" /><span className="min-w-0"><span className="block font-mono text-[10px] sm:text-xs tracking-widest uppercase whitespace-nowrap">Request Clearance</span><span className="block font-mono text-[10px] opacity-80 mt-0.5 whitespace-nowrap">Make account</span></span></button></Link>
            <Link href="/login"><button className="w-full min-h-14 inline-flex items-center gap-2 border border-border text-foreground px-3 py-2.5 hover:border-primary/50 transition-all text-left" data-testid="button-login"><Lock className="w-4 h-4 flex-shrink-0" /><span className="min-w-0"><span className="block font-mono text-[10px] sm:text-xs tracking-widest uppercase whitespace-nowrap">Access Terminal</span><span className="block font-mono text-[10px] text-muted-foreground mt-0.5 whitespace-nowrap">Login</span></span></button></Link>
            <a href="#community" className="w-full min-h-14 inline-flex items-center gap-2 border border-primary/40 bg-primary/5 text-primary px-3 py-2.5 hover:border-primary/70 hover:bg-primary/10 transition-all text-left"><Bug className="w-4 h-4 flex-shrink-0" /><span className="min-w-0"><span className="block font-mono text-[10px] sm:text-xs tracking-widest uppercase whitespace-nowrap">Join Audit</span><span className="block font-mono text-[10px] opacity-80 mt-0.5 whitespace-nowrap">Review security</span></span></a>
            <a href={GITHUB_URL} target="_blank" rel="noreferrer" className="w-full min-h-14 inline-flex items-center gap-2 border border-border text-foreground px-3 py-2.5 hover:border-primary/50 transition-all text-left"><Github className="w-4 h-4 flex-shrink-0" /><span className="min-w-0"><span className="block font-mono text-[10px] sm:text-xs tracking-widest uppercase whitespace-nowrap">GitHub</span><span className="block font-mono text-[10px] text-muted-foreground mt-0.5 whitespace-nowrap">View source</span></span></a>
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

      <section id="local-device-exposure" className="py-24 px-6 border-y border-border/50 bg-background">
        <div className="max-w-7xl mx-auto">
          <div className="grid grid-cols-1 lg:grid-cols-[0.9fr_1.1fr] gap-8 items-start mb-10">
            <div>
              <div className="font-mono text-xs text-primary tracking-widest mb-3">LOCAL DEVICE EXPOSURE</div>
              <h2 className="font-mono font-bold text-3xl md:text-5xl leading-tight mb-5">Did you know your iMessage & Signal chats are readable in plaintext by anyone or any AI who uses your computer or phone?</h2>
              <p className="font-mono text-sm text-muted-foreground leading-relaxed">
                Transport encryption does not protect plaintext after your device receives it. If an AI agent, remote admin tool, malware process, phone malware, or person has access to your unlocked computer or phone, the practical question becomes what is already on disk, in app storage, in notifications, in previews, or visible on screen. <span className="text-destructive underline decoration-destructive/70 underline-offset-4">If plaintext exists there, a bad actor can instantly copy or upload all your texts, attachments, contacts, and years of history without your knowledge.</span> QuantumShield's claim is source-auditable: check GitHub and verify the storage, key, and reveal paths yourself.
              </p>
            </div>
            <div className="border border-destructive/35 bg-destructive/5 p-5">
              <div className="flex items-start gap-3">
                <AlertTriangle className="w-5 h-5 text-destructive mt-0.5 flex-shrink-0" />
                <div>
                  <div className="font-mono text-xs text-destructive tracking-widest mb-2">UNLOCKED DEVICE WARNING</div>
                  <p className="font-mono text-xs text-muted-foreground leading-relaxed">
                    No messenger can guarantee secrecy from software already running with your user privileges on a computer or phone. QuantumShield narrows the normal on-disk and on-screen plaintext window so there is less for a bad actor to silently copy or upload; it does not defeat a fully compromised endpoint while you are actively revealing secrets.
                  </p>
                </div>
              </div>
            </div>
          </div>

          <div className="grid grid-cols-1 lg:grid-cols-3 gap-4">
            {LOCAL_DEVICE_EXPOSURE.map((item) => (
              <div key={item.name} className="border border-border/50 bg-card/30 p-5">
                <div className="text-primary mb-4">{item.icon}</div>
                <div className="font-mono text-[10px] text-muted-foreground tracking-widest mb-2">{item.name.toUpperCase()}</div>
                <h3 className={`font-mono text-base font-bold leading-snug mb-2 ${item.tone === "benefit" ? "text-foreground" : "text-destructive"}`}>{item.plain}</h3>
                <p className="font-mono text-xs text-muted-foreground leading-relaxed mb-4">{item.headline}</p>
                <div className="space-y-4">
                  {[
                    { label: "RAM while running", icon: <Cpu className="w-4 h-4" />, plain: item.runningPlain, lines: item.running },
                    { label: "Disk while not running", icon: <HardDrive className="w-4 h-4" />, plain: item.stoppedPlain, lines: item.stopped },
                  ].map((group) => (
                    <div key={group.label} className="border border-border/40 bg-background/35 p-3">
                      <div className="flex items-center gap-2 mb-3">
                        <span className={item.tone === "benefit" ? "text-primary" : "text-destructive"}>{group.icon}</span>
                        <div className="font-mono text-[10px] text-muted-foreground tracking-widest">{group.label.toUpperCase()}</div>
                      </div>
                      <p className={`font-mono text-sm font-bold leading-snug mb-2 ${item.tone === "benefit" ? "text-foreground" : "text-destructive"}`}>{group.plain}</p>
                      <div className="space-y-2">
                        {group.lines.map((line) => (
                          <div key={line} className="grid grid-cols-[auto_1fr] gap-2">
                            <span className={`mt-1.5 h-1.5 w-1.5 ${item.tone === "benefit" ? "bg-primary" : "bg-destructive"}`} />
                            <p className="font-mono text-xs text-muted-foreground/80 leading-relaxed">{line}</p>
                          </div>
                        ))}
                      </div>
                    </div>
                  ))}
                  <div className={`border p-3 ${item.tone === "benefit" ? "border-primary/30 bg-primary/5" : "border-destructive/30 bg-destructive/5"}`}>
                    <div className={`font-mono text-[10px] tracking-widest mb-2 ${item.tone === "benefit" ? "text-primary" : "text-destructive"}`}>AI AGENT / MALWARE IMPLICATION</div>
                    <p className={`font-mono text-sm font-bold leading-snug mb-2 ${item.tone === "benefit" ? "text-foreground" : "text-destructive"}`}>{item.implicationPlain}</p>
                    <p className="font-mono text-xs text-muted-foreground/80 leading-relaxed">{item.implication}</p>
                  </div>
                </div>
              </div>
            ))}
          </div>
        </div>
      </section>

      <section id="security-model" className="py-24 px-6 border-y border-border/50 bg-card/20">
        <div className="max-w-7xl mx-auto">
          <div className="grid grid-cols-1 lg:grid-cols-[0.9fr_1.1fr] gap-10 items-start mb-12">
            <div>
              <div className="font-mono text-xs text-primary tracking-widest mb-3">CORE PRIVATE MESSENGER PROBLEM</div>
              <h2 className="font-mono font-bold text-3xl md:text-5xl leading-tight mb-5">
                The core problem with private messengers is that they only protect message contents, not the people sending them.
              </h2>
              <p className="font-mono text-sm text-muted-foreground leading-relaxed mb-5">
                QuantumShield uses passkeys so account access is mediated by the same class of platform authenticator native apps rely on. On supported Apple hardware, that means Face ID, Touch ID, device passcode policy, Keychain, and Secure Enclave-backed protection for the private passkey material.
              </p>
              <p className="font-mono text-sm text-muted-foreground leading-relaxed">
                The point is not to ask the browser for native-only powers. The point is to design defenses that work everywhere the web can run: post-quantum message packages, deliberate reveal, local capture awareness, and open distribution that auditors can inspect immediately.
              </p>
            </div>
            <div className="border border-primary/25 bg-background/70 p-5">
              <div className="grid grid-cols-[1fr_auto_1fr_auto_1fr] items-center gap-2">
                {[
                  { icon: <MousePointerClick className="w-5 h-5" />, label: "Hold" },
                  { icon: <Shield className="w-5 h-5" />, label: "Verify" },
                  { icon: <Lock className="w-5 h-5" />, label: "Decrypt" },
                ].map((step, index) => (
                  <Fragment key={step.label}>
                    <div className="border border-border/60 bg-card/40 p-4 min-h-28 flex flex-col items-center justify-center text-center">
                      <div className="text-primary mb-3">{step.icon}</div>
                      <div className="font-mono text-xs tracking-widest">{step.label}</div>
                      <div className="font-mono text-[10px] text-muted-foreground mt-2 leading-snug">
                        {index === 0 ? "User intent" : index === 1 ? "Post-quantum signature" : "Temporary plaintext"}
                      </div>
                    </div>
                    {index < 2 && <ChevronRight className="w-4 h-4 text-primary/70" />}
                  </Fragment>
                ))}
              </div>
              <div className="mt-4 border border-border/50 bg-card/30 p-4">
                <div className="font-mono text-[10px] tracking-widest text-primary mb-2">MESSAGE PACKAGE</div>
                <div className="grid grid-cols-1 sm:grid-cols-3 gap-2">
                  <div className="border border-border/40 px-3 py-2 font-mono text-[10px] text-muted-foreground">AES ciphertext</div>
                  <div className="border border-border/40 px-3 py-2 font-mono text-[10px] text-muted-foreground">ML-KEM wrapped keys</div>
                  <div className="border border-border/40 px-3 py-2 font-mono text-[10px] text-muted-foreground">ML-DSA signature</div>
                </div>
              </div>
            </div>
          </div>

          <div className="grid grid-cols-1 lg:grid-cols-2 gap-4 mb-10">
            <div className="border border-border/50 bg-background/60 p-5">
              <div className="font-mono text-xs text-primary tracking-widest mb-4">CRYPTOGRAPHIC ROLES</div>
              <div className="space-y-3">
                {CRYPTO_ROLES.map((item) => (
                  <div key={item.name} className="grid grid-cols-[auto_1fr] gap-3 border border-border/40 bg-card/25 p-4">
                    <div className="text-primary">{item.icon}</div>
                    <div>
                      <div className="font-mono text-sm font-semibold">{item.name}</div>
                      <div className="font-mono text-[10px] text-muted-foreground mt-1">{item.expanded}</div>
                      <p className="font-mono text-xs text-muted-foreground leading-relaxed mt-2">{item.role}</p>
                    </div>
                  </div>
                ))}
              </div>
            </div>
            <div className="border border-border/50 bg-background/60 p-5">
              <div className="font-mono text-xs text-primary tracking-widest mb-4">WHAT THIS DOES DIFFERENTLY</div>
              <div className="grid grid-cols-1 sm:grid-cols-2 gap-3">
                {DISTRIBUTION_DEFENSES.map((item) => (
                  <div key={item.title} className="border border-border/40 bg-card/25 p-4">
                    <div className="text-primary mb-3">{item.icon}</div>
                    <div className="font-mono text-sm font-semibold mb-2">{item.title}</div>
                    <p className="font-mono text-xs text-muted-foreground leading-relaxed">{item.copy}</p>
                  </div>
                ))}
              </div>
            </div>
          </div>

          <div className="border border-border/50 bg-background/60 p-5">
            <div className="grid grid-cols-1 lg:grid-cols-[0.85fr_1.15fr] gap-6 items-start mb-8">
              <div>
                <div className="font-mono text-xs text-primary tracking-widest mb-3">SIGNAL / IMESSAGE / QUANTUMSHIELD</div>
                <h3 className="font-mono font-bold text-2xl md:text-3xl leading-tight mb-4">What each app exposes in real life.</h3>
                <p className="font-mono text-sm text-muted-foreground leading-relaxed">
                  This is the plain-English version: what you do, what the app stores or routes, and what a nation-state can still learn even when message content stays encrypted.
                </p>
              </div>
              <div className="border border-destructive/35 bg-destructive/5 p-4">
                <div className="flex items-start gap-3">
                  <AlertTriangle className="w-5 h-5 text-destructive mt-0.5 flex-shrink-0" />
                  <div>
                    <div className="font-mono text-xs text-destructive tracking-widest mb-2">ASSUME TOTAL COLLECTION</div>
                    <p className="font-mono text-xs text-muted-foreground leading-relaxed">
                      Model the attacker as storing every packet, push event, login, device registration, retry, room event, and ciphertext forever. Content encryption helps, but metadata, identity, screenshots, backups, and endpoint exposure are separate battles.
                    </p>
                  </div>
                </div>
              </div>
            </div>

            <div className="space-y-4">
              {PROTOCOL_COMPARISON.map((row, index) => (
                <div key={row.stage} className="border border-border/50 bg-card/25">
                  <div className="grid grid-cols-1 xl:grid-cols-[220px_1fr_1fr_1fr]">
                    <div className="border-b xl:border-b-0 xl:border-r border-border/40 p-4 bg-background/45">
                      <div className="text-primary mb-3">{row.icon}</div>
                      <div className="font-mono text-[10px] text-primary tracking-widest mb-2">LAYER {String(index + 1).padStart(2, "0")}</div>
                      <div className="font-mono text-sm font-bold">{row.stage}</div>
                    </div>
                    {[
                      { label: "QuantumShield", headline: row.quantumShieldLead, copy: row.quantumShield, tone: "benefit" },
                      { label: "Signal", headline: row.signalLead, copy: row.signal, tone: "risk" },
                      { label: "iMessage", headline: row.imessageLead, copy: row.imessage, tone: "risk" },
                    ].map((item) => (
                      <div key={item.label} className="border-b xl:border-b-0 xl:border-r last:border-r-0 border-border/40 p-4">
                        <div className="font-mono text-[10px] text-muted-foreground tracking-widest mb-2">{item.label.toUpperCase()}</div>
                        <div className={`font-mono text-sm font-bold leading-snug mb-3 ${item.tone === "benefit" ? "text-foreground" : "text-destructive"}`}>{item.headline}</div>
                        <p className="font-mono text-xs text-muted-foreground leading-relaxed">{item.copy}</p>
                      </div>
                    ))}
                  </div>
                  <div className="border-t border-destructive/25 bg-destructive/5 p-4">
                    <div className="flex items-start gap-2">
                      <AlertTriangle className="w-4 h-4 text-destructive mt-0.5 flex-shrink-0" />
                      <p className="font-mono text-xs text-muted-foreground leading-relaxed">{row.warning}</p>
                    </div>
                  </div>
                </div>
              ))}
            </div>

            <div className="mt-6 border border-border/50 bg-card/25 p-4">
              <div className="font-mono text-xs text-primary tracking-widest mb-3">PUBLIC REFERENCES</div>
              <div className="flex flex-wrap gap-2">
                {PROTOCOL_REFERENCES.map((item) => (
                  <a key={item.href} href={item.href} target="_blank" rel="noreferrer" className="inline-flex items-center gap-2 border border-border bg-background px-3 py-2 font-mono text-[10px] text-muted-foreground hover:text-foreground hover:border-primary/50 transition-colors uppercase tracking-widest">
                    {item.label}
                    <ExternalLink className="w-3 h-3" />
                  </a>
                ))}
              </div>
            </div>
          </div>
        </div>
      </section>

      <section id="privacy-stack" className="py-24 px-6 border-y border-border/50 bg-background">
        <div className="max-w-7xl mx-auto">
          <div className="max-w-3xl mb-14">
            <div className="font-mono text-xs text-primary tracking-widest mb-3">PRIVACY STACK</div>
            <h2 className="font-mono font-bold text-3xl md:text-5xl leading-tight mb-5">Privacy features most messaging apps never combine.</h2>
            <p className="font-mono text-sm text-muted-foreground leading-relaxed">QuantumShield is built around the moment of exposure: the camera watching the screen, the unfocused tab, the screenshot key, the shoulder glance, and the stale message whose usable key path expires into unreadable ciphertext. Check the source code and verify the timed key purge.</p>
          </div>
          <div className="grid grid-cols-1 md:grid-cols-2 xl:grid-cols-3 gap-4">
            {PRIVACY_FEATURES.map((feature) => <div key={feature.title} className="border border-border/50 bg-card/30 p-5"><div className="text-primary mb-4">{feature.icon}</div><h3 className="font-mono text-sm font-semibold mb-3">{feature.title}</h3><p className="font-mono text-xs text-muted-foreground leading-relaxed">{feature.desc}</p></div>)}
          </div>
        </div>
      </section>

      <section id="ethos" className="py-24 px-6 border-y border-border/50 bg-card/20"><div className="max-w-5xl mx-auto"><div className="font-mono text-xs text-primary tracking-widest mb-4">ETHOS / EXPERIMENT</div><h2 className="font-mono font-bold text-3xl md:text-5xl leading-tight mb-8">What is the most secure ideal form of truly ephemeral digital communication?</h2><div className="grid grid-cols-1 lg:grid-cols-[1.2fr_0.8fr] gap-8 items-start"><p className="font-mono text-sm md:text-base text-muted-foreground leading-relaxed">QuantumShield is our working answer to that question. The mission is to build communication software where messages can be encrypted for the quantum era, revealed only with deliberate user intent, and made practically useless after expiry. We are testing whether communities can rely on open, auditable software for private coordination without asking anyone to trust a black box.</p><div className="border border-border/50 bg-background/50 p-6"><p className="font-mono text-xs text-muted-foreground leading-relaxed mb-5">The experiment is public by design: inspect the code, challenge the threat model, report weak assumptions, and help us move closer to dependable ephemeral messaging.</p><div className="flex flex-col sm:flex-row lg:flex-col gap-3"><a href={GITHUB_URL} target="_blank" rel="noreferrer" className="inline-flex items-center justify-center gap-2 border border-border text-foreground font-mono text-xs px-5 py-3 hover:border-primary/50 transition-all tracking-widest uppercase"><Github className="w-4 h-4" />SOURCE</a><a href={SECURITY_URL} target="_blank" rel="noreferrer" className="inline-flex items-center justify-center gap-2 bg-primary text-primary-foreground font-mono text-xs px-5 py-3 hover:bg-primary/90 transition-all tracking-widest uppercase"><Bug className="w-4 h-4" />AUDIT</a></div></div></div></div></section>

      <section id="features" className="py-24 px-6 border-t border-border/50"><div className="max-w-7xl mx-auto"><div className="text-center mb-16"><div className="font-mono text-xs text-primary tracking-widest mb-3">CAPABILITIES</div><h2 className="font-mono font-bold text-3xl md:text-4xl">Security without compromise</h2><p className="font-mono text-sm text-muted-foreground mt-4 max-w-xl mx-auto">Every feature was designed assuming your adversary has a quantum computer.</p></div><div className="grid grid-cols-1 md:grid-cols-2 lg:grid-cols-3 gap-4">{FEATURES.map((f) => <div key={f.title} className="border border-border/50 bg-card/30 p-6 hover:border-primary/30 hover:bg-card/60 transition-all group"><div className="text-primary mb-4 group-hover:scale-110 transition-transform w-fit">{f.icon}</div><h3 className="font-mono font-semibold text-sm tracking-wide mb-3">{f.title}</h3><p className="font-mono text-xs text-muted-foreground leading-relaxed">{f.desc}</p></div>)}</div></div></section>

      <section id="security" className="py-24 px-6 bg-card/20 border-y border-border/50"><div className="max-w-7xl mx-auto"><div className="grid grid-cols-1 lg:grid-cols-2 gap-16 items-center"><div><div className="font-mono text-xs text-primary tracking-widest mb-3">CRYPTOGRAPHIC STACK</div><h2 className="font-mono font-bold text-3xl md:text-4xl mb-6">Every layer verified.<br />Every key quantum-safe.</h2><p className="font-mono text-sm text-muted-foreground mb-8 leading-relaxed">QuantumShield uses only NIST-finalized post-quantum algorithms. No experimental schemes. No proprietary curves. Pure, auditable, open-standard cryptography.</p><p className="font-mono text-sm text-muted-foreground leading-relaxed">When a message expires, clients purge local message keys and the API wipes wrapped key envelopes. The ciphertext can remain on the server — permanently locked. No court order, no quantum computer, no brute force attack can recover it without a usable key path.</p></div><div className="space-y-2">{ALGORITHMS.map((alg) => <div key={alg.name} className="flex items-center justify-between border border-border/50 bg-card/50 px-5 py-4" data-testid={`algo-${alg.name}`}><div><div className="font-mono font-bold text-sm">{alg.name}</div><div className="font-mono text-xs text-muted-foreground">{alg.spec} — {alg.type}</div></div><div className="flex items-center gap-2"><span className="w-2 h-2 bg-primary rounded-full animate-pulse" /><span className="font-mono text-xs text-primary">{alg.status}</span></div></div>)}<div className="border border-border/50 bg-card/50 px-5 py-4 font-mono text-xs text-muted-foreground leading-relaxed"><span className="text-primary">// </span>Triple-layer: PQ key exchange + PQ signatures + AES-256-GCM. Breaking one layer is mathematically insufficient.</div></div></div></div></section>

      <section className="py-24 px-6 border-t border-border/50"><div className="max-w-7xl mx-auto"><div className="text-center mb-16"><div className="font-mono text-xs text-primary tracking-widest mb-3">THREAT MODEL</div><h2 className="font-mono font-bold text-3xl md:text-4xl">Designed for worst-case adversaries</h2></div><div className="grid grid-cols-1 md:grid-cols-3 gap-4">{[{ threat: "Quantum Computer", defense: "ML-KEM-1024 + ML-DSA-87 resist known quantum attacks including Shor's algorithm." }, { threat: "Physical Observation", defense: "On-device camera detection blanks the screen when a recording device enters the frame." }, { threat: "Screenshot / Screen Recording", defense: "PWAs cannot receive true iOS or Chrome screenshot callbacks. QuantumShield minimizes exposure with hold-to-reveal, blur/background shielding, print/clipboard blocking, browser capture warnings, and camera-based recording-device detection." }, { threat: "Server Compromise", defense: "End-to-end encrypted. The server sees only ciphertext — never plaintext. Ever." }, { threat: "Retroactive Decryption", defense: "Expired message keys and wrapped key envelopes are purged on a timer. Old ciphertext is cryptographically irrecoverable without a usable key path." }, { threat: "Supply Chain Attack", defense: "Fully open source. Every dependency is auditable. Run your own server." }].map((t) => <div key={t.threat} className="border border-border/50 bg-card/30 p-6"><div className="flex items-center gap-2 mb-3"><Zap className="w-4 h-4 text-destructive" /><span className="font-mono text-xs font-semibold text-destructive">{t.threat}</span></div><p className="font-mono text-xs text-muted-foreground leading-relaxed">{t.defense}</p></div>)}</div></div></section>

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
