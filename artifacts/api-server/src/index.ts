import { config as loadDotenv } from "dotenv";
import { resolve } from "path";

if (!process.env["REPL_ID"]) {
  loadDotenv({ path: resolve(process.cwd(), "../../.env"), quiet: true });
}

const app = (await import("./app")).default;
const { logger } = await import("./lib/logger");

const rawPort = process.env["PORT"];

if (!rawPort) {
  throw new Error(
    "PORT environment variable is required but was not provided.",
  );
}

const port = Number(rawPort);

if (Number.isNaN(port) || port <= 0) {
  throw new Error(`Invalid PORT value: "${rawPort}"`);
}

app.listen(port, (err) => {
  if (err) {
    logger.error({ err }, "Error listening on port");
    process.exit(1);
  }

  logger.info({ port }, "Server listening");
});
