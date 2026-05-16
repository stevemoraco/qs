import { Router, type IRouter } from "express";
import healthRouter from "./health";
import authRouter from "./auth";
import usersRouter from "./users";
import roomsRouter from "./rooms";
import messagesRouter from "./messages";
import keysRouter from "./keys";
import statsRouter from "./stats";
import pushRouter from "./push";
import leadsRouter from "./leads";

const router: IRouter = Router();

router.use(healthRouter);
router.use(authRouter);
router.use(usersRouter);
router.use(roomsRouter);
router.use(messagesRouter);
router.use(keysRouter);
router.use(statsRouter);
router.use(pushRouter);
router.use(leadsRouter);

export default router;
