import { Router } from "express";
import { db, leadsTable } from "@workspace/db";
import { sql } from "drizzle-orm";
import { PostLeadsBody } from "@workspace/api-zod";

const router = Router();

function cleanOptional(value: string | null | undefined): string | null {
  const trimmed = value?.trim();
  return trimmed ? trimmed : null;
}

router.post("/leads", async (req, res) => {
  const parse = PostLeadsBody.safeParse(req.body);
  if (!parse.success) {
    res.status(400).json({ error: parse.error.message });
    return;
  }

  const { step } = parse.data;
  const email = parse.data.email.trim().toLowerCase();
  const now = new Date();

  const [lead] = await db
    .insert(leadsTable)
    .values({
      email,
      currentStep: step,
      name: cleanOptional(parse.data.name),
      phone: cleanOptional(parse.data.phone),
      organization: cleanOptional(parse.data.organization),
      title: cleanOptional(parse.data.title),
      source: cleanOptional(parse.data.source) ?? "homepage",
      updatedAt: now,
    })
    .onConflictDoUpdate({
      target: leadsTable.email,
      set: {
        currentStep: sql`greatest(${leadsTable.currentStep}, ${step})`,
        name: sql`coalesce(excluded.name, ${leadsTable.name})`,
        phone: sql`coalesce(excluded.phone, ${leadsTable.phone})`,
        organization: sql`coalesce(excluded.organization, ${leadsTable.organization})`,
        title: sql`coalesce(excluded.title, ${leadsTable.title})`,
        source: sql`coalesce(excluded.source, ${leadsTable.source})`,
        updatedAt: now,
      },
    })
    .returning();

  res.json(lead);
});

export default router;
