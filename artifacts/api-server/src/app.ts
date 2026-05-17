import express, { type ErrorRequestHandler, type Express } from "express";
import cors from "cors";
import pinoHttp from "pino-http";
import router from "./routes";
import { logger } from "./lib/logger";
import { startPushNotificationWorker } from "./routes/push";
import { recordErrorLog } from "./lib/error-log";

const app: Express = express();
app.disable("etag");

function allowedOrigins(): string[] {
  return (process.env["CORS_ORIGINS"] ?? "")
    .split(",")
    .map((origin) => origin.trim())
    .filter(Boolean);
}

function normalizeOrigin(origin: string): string | null {
  try {
    return new URL(origin).origin;
  } catch {
    return null;
  }
}

function configuredAllowedOrigins(): Set<string> {
  return new Set(allowedOrigins().map(normalizeOrigin).filter((origin): origin is string => !!origin));
}

app.disable("x-powered-by");
app.use((_req, res, next) => {
  res.setHeader("X-Content-Type-Options", "nosniff");
  res.setHeader("Referrer-Policy", "no-referrer");
  res.setHeader("Permissions-Policy", "camera=(self), microphone=(), geolocation=()");
  res.setHeader("Cross-Origin-Opener-Policy", "same-origin");
  res.setHeader("Cross-Origin-Resource-Policy", "same-origin");
  if (process.env.NODE_ENV === "production") {
    res.setHeader("Strict-Transport-Security", "max-age=31536000; includeSubDomains; preload");
  }
  next();
});

app.use("/api", (_req, res, next) => {
  res.setHeader("Cache-Control", "no-store, max-age=0");
  res.setHeader("Pragma", "no-cache");
  next();
});

app.use(
  pinoHttp({
    logger,
    serializers: {
      req(req) {
        return {
          id: req.id,
          method: req.method,
          url: req.url?.split("?")[0],
        };
      },
      res(res) {
        return {
          statusCode: res.statusCode,
        };
      },
    },
  }),
);
app.use(cors({
  origin(origin, callback) {
    if (!origin) {
      callback(null, true);
      return;
    }
    const normalizedOrigin = normalizeOrigin(origin);
    const configured = configuredAllowedOrigins();
    if (configured.size === 0) {
      callback(null, process.env.NODE_ENV !== "production");
      return;
    }
    callback(null, !!normalizedOrigin && configured.has(normalizedOrigin));
  },
}));
app.use(express.json({ limit: "256kb" }));
app.use(express.urlencoded({ extended: true, limit: "64kb" }));

app.use("/api", router);

const apiErrorHandler: ErrorRequestHandler = (err, req, res, _next) => {
  const status = typeof err?.status === "number" && err.status >= 400 && err.status < 600
    ? err.status
    : 500;
  logger.error({
    err,
    method: req.method,
    path: req.path,
    statusCode: status,
  }, "API request failed");
  void recordErrorLog({
    source: "server",
    level: "error",
    code: status === 500 ? "INTERNAL_SERVER_ERROR" : "REQUEST_FAILED",
    message: err instanceof Error ? err.message : "API request failed",
    method: req.method,
    path: req.path,
    statusCode: status,
    userId: typeof (req as { userId?: unknown }).userId === "string" ? (req as unknown as { userId: string }).userId : null,
    clientCommit: req.header("x-qs-client-commit") ?? null,
    clientVersion: req.header("x-qs-client-version") ?? null,
    details: {
      name: err instanceof Error ? err.name : typeof err,
    },
  });
  if (res.headersSent) return;
  res.status(status).json({
    error: status === 500 ? "Internal server error" : "Request failed",
    code: status === 500 ? "INTERNAL_SERVER_ERROR" : "REQUEST_FAILED",
  });
};

app.use("/api", apiErrorHandler);

if (process.env["QS_DISABLE_BACKGROUND_WORKERS"] !== "1") {
  startPushNotificationWorker();
}

export default app;
