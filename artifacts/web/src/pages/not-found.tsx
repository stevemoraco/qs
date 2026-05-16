import { Link } from "wouter";
import { Shield } from "lucide-react";

export default function NotFound() {
  return (
    <div className="min-h-screen bg-background flex items-center justify-center px-4">
      <div className="text-center">
        <div className="font-mono text-8xl font-bold text-primary/20 mb-6">404</div>
        <h1 className="font-mono font-bold text-2xl mb-4">PAGE NOT FOUND</h1>
        <p className="font-mono text-sm text-muted-foreground mb-8">
          This sector of the network doesn't exist.
        </p>
        <Link href="/">
          <button className="inline-flex items-center gap-2 bg-primary text-primary-foreground font-mono text-xs tracking-widest px-6 py-3 hover:bg-primary/90 transition-all uppercase">
            <Shield className="w-4 h-4" />
            RETURN TO BASE
          </button>
        </Link>
      </div>
    </div>
  );
}
