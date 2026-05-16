import { Router } from "express";
import { db, pushSubscriptionsTable } from "@workspace/db";
import { and, eq } from "drizzle-orm";
import webPush from "web-push";
import { requireAuth, type AuthRequest } from "../middlewares/auth";

const router = Router();

// Allowlist of recognized Web Push service hosts. Blocks SSRF via arbitrary
// endpoints stored here and later fetched by web-push.
const PUSH_HOST_PATTERNS = [
  /\.push\.services\.mozilla\.com$/,
  /\.googleapis\.com$/, // fcm.googleapis.com
  /\.notify\.windows\.com$/,
  /\.push\.apple\.com$/,
  /\.web\.push\.apple\.com$/,
];

function isValidPushEndpoint(raw: string): boolean {
  let url: URL;
  try {
    url = new URL(raw);
  } catch {
    return false;
  }
  if (url.protocol !== "https:") return false;
  const host = url.hostname.toLowerCase();
  if (
    host === "localhost" ||
    host.endsWith(".local") ||
    /^\d+\.\d+\.\d+\.\d+$/.test(host) ||
    host.includes(":")
  ) {
    return false;
  }
  return PUSH_HOST_PATTERNS.some((re) => re.test(host));
}

export function configureWebPush(): boolean {
  const publicKey = process.env["VAPID_PUBLIC_KEY"];
  const privateKey = process.env["VAPID_PRIVATE_KEY"];
  const subject = process.env["VAPID_SUBJECT"];

  if (!publicKey || !privateKey || !subject) return false;

  webPush.setVapidDetails(subject, publicKey, privateKey);
  return true;
}

export async function notifyUser(userId: string, payload: { title: string; body: string; url?: string; tag?: string }) {
  if (!configureWebPush()) return;

  const subscriptions = await db
    .select()
    .from(pushSubscriptionsTable)
    .where(eq(pushSubscriptionsTable.userId, userId));

  await Promise.allSettled(
    subscriptions.map(async (sub) => {
      try {
        await webPush.sendNotification(
          {
            endpoint: sub.endpoint,
            keys: {
              p256dh: sub.p256dh,
              auth: sub.auth,
            },
          },
          JSON.stringify(payload),
        );
      } catch (err) {
        const statusCode = (err as { statusCode?: number }).statusCode;
        if (statusCode === 404 || statusCode === 410) {
          await db.delete(pushSubscriptionsTable).where(eq(pushSubscriptionsTable.endpoint, sub.endpoint));
        }
      }
    }),
  );
}

router.get("/push/vapid-public-key", (_req, res) => {
  const key = process.env["VAPID_PUBLIC_KEY"];
  if (!key) {
    res.status(503).json({ error: "Push notifications not configured" });
    return;
  }
  res.json({ publicKey: key });
});

router.post("/push/subscribe", requireAuth, async (req: AuthRequest, res) => {
  const { endpoint, keys, userAgent } = req.body ?? {};

  if (typeof endpoint !== "string" || !keys || typeof keys.p256dh !== "string" || typeof keys.auth !== "string") {
    res.status(400).json({ error: "Invalid push subscription payload" });
    return;
  }

  if (!isValidPushEndpoint(endpoint)) {
    res.status(400).json({ error: "Endpoint is not a recognized Web Push service" });
    return;
  }

  const existing = await db
    .select({ id: pushSubscriptionsTable.id })
    .from(pushSubscriptionsTable)
    .where(eq(pushSubscriptionsTable.endpoint, endpoint))
    .limit(1);

  if (existing.length > 0) {
    await db
      .update(pushSubscriptionsTable)
      .set({
        userId: req.user!.id,
        p256dh: keys.p256dh,
        auth: keys.auth,
        userAgent: typeof userAgent === "string" ? userAgent : null,
      })
      .where(eq(pushSubscriptionsTable.endpoint, endpoint));
  } else {
    await db.insert(pushSubscriptionsTable).values({
      userId: req.user!.id,
      endpoint,
      p256dh: keys.p256dh,
      auth: keys.auth,
      userAgent: typeof userAgent === "string" ? userAgent : null,
    });
  }

  res.status(201).json({ ok: true });
});

router.delete("/push/subscribe", requireAuth, async (req: AuthRequest, res) => {
  const { endpoint } = req.body ?? {};
  if (typeof endpoint !== "string") {
    res.status(400).json({ error: "endpoint required" });
    return;
  }
  await db
    .delete(pushSubscriptionsTable)
    .where(
      and(
        eq(pushSubscriptionsTable.endpoint, endpoint),
        eq(pushSubscriptionsTable.userId, req.user!.id),
      ),
    );
  res.json({ ok: true });
});

export default router;
