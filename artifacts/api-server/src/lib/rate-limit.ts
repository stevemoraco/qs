type RateEntry = {
  count: number;
  resetAt: number;
  lockedUntil: number;
};

const buckets = new Map<string, RateEntry>();

export function consumeRateLimit(
  key: string,
  limit: number,
  windowMs: number,
  lockMs: number
): boolean {
  const now = Date.now();
  const current = buckets.get(key);

  if (current?.lockedUntil && current.lockedUntil > now) return false;

  const entry = current && current.resetAt > now
    ? current
    : { count: 0, resetAt: now + windowMs, lockedUntil: 0 };

  entry.count += 1;
  if (entry.count > limit) {
    entry.lockedUntil = now + lockMs;
    buckets.set(key, entry);
    return false;
  }

  buckets.set(key, entry);
  return true;
}

