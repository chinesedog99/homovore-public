package dev.leonetic.features.modules.combat;

import dev.leonetic.Homovore;
import dev.leonetic.event.impl.entity.player.TickEvent;
import dev.leonetic.event.impl.render.Render3DEvent;
import dev.leonetic.event.system.Subscribe;
import dev.leonetic.features.modules.Module;
import dev.leonetic.features.modules.client.TargetsModule;
import dev.leonetic.features.modules.world.SpeedMineModule;
import dev.leonetic.features.settings.Setting;
import dev.leonetic.util.PlaceUtil;
import dev.leonetic.util.inventory.InventoryUtil;
import dev.leonetic.util.inventory.ResultType;
import dev.leonetic.util.render.RenderUtil;
import net.minecraft.core.BlockPos;
import net.minecraft.core.Direction;
import net.minecraft.util.Mth;
import net.minecraft.world.entity.LivingEntity;
import net.minecraft.world.entity.player.Player;
import net.minecraft.world.item.Items;
import net.minecraft.world.phys.AABB;
import net.minecraft.world.phys.Vec3;

import java.awt.Color;
import java.util.ArrayList;
import java.util.Comparator;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

public class AutoTrapModule extends Module {

    private final Setting<Double> range      = num("TargetRange", 8.0, 1.0, 16.0).setPage("General");
    private final Setting<Double> reach      = num("Reach", 5.5, 3.0, 6.0).setPage("General");
    private final Setting<Boolean> selfToggle = bool("SelfToggle", true).setPage("General");
    private final Setting<Boolean> debug      = bool("Debug", false).setPage("General");

    private final Setting<Boolean> render     = bool("Render", true).setPage("Render");
    private final Setting<Float> lineWidth    = num("LineWidth", 1.0f, 0.5f, 5.0f).setPage("Render");
    private final Setting<Color> fillColor    = color("FillColor", 255, 50, 50, 45).setPage("Render");
    private final Setting<Color> outlineColor = color("OutlineColor", 255, 50, 50, 160).setPage("Render");

    private final Set<BlockPos> wanted = new HashSet<>(16);
    private final Set<BlockPos> owned  = new HashSet<>(16);
    private final List<BlockPos> order   = new ArrayList<>(16);
    private final List<BlockPos> scratch = new ArrayList<>(16);

    private static final long RESEND_MS = 250L;
    private static final long RETRY_RESET_MS = 1_500L;
    private static final int MAX_SEND_ATTEMPTS = 4;
    private final Map<BlockPos, Long> sentAt = new HashMap<>();
    private final Map<BlockPos, Integer> sendAttempts = new HashMap<>();

    private static final double MAX_SAMPLE_SPEED = 8.0;
    private static final double MAX_PREDICT_DISTANCE = 3.5;
    private static final double MAX_ELYTRA_PREDICT_DISTANCE = 5.0;
    private static final double[] CAGE_BACKOFF = {1.0, 0.75, 0.5, 0.25, 0.0};
    private static final double[] ELYTRA_CAGE_BACKOFF = {1.0, 0.75};
    private static final double[] LOCKED_CAGE_BACKOFF = {1.0};
    private static final int MIN_ELYTRA_LOCK_CELLS = 1;
    private static final int ELYTRA_LOCK_TICKS = 8;
    private static final double ELYTRA_IMPACT_SPEED = 0.8;

    private java.util.UUID trackedId;
    private Vec3 prevPos;
    private Vec3 filteredVelocity = Vec3.ZERO;
    private Vec3 velocityChange = Vec3.ZERO;
    private Vec3 lockedElytraFeet;
    private int elytraLockTicks;
    private int satisfiedCells;

    public AutoTrapModule() {
        super("AutoTrap", "Predicts a target's path and encases them with airplaced blocks.", Category.COMBAT);
    }

    @Override
    public void onDisable() {
        pruneAll();
        resetTracking();
    }

    @Subscribe(priority = 1)
    private void onTick(TickEvent event) {
        if (nullCheck()) {
            pruneAll();
            resetTracking();
            return;
        }
        if (mc.screen != null) {
            pruneAll();
            resetTracking();
            return;
        }

        int slot = resolveSlot();
        if (slot < 0) {
            pruneAll();
            resetTracking();
            return;
        }

        LivingEntity target = findTarget();
        if (target == null) {
            pruneAll();
            resetTracking();
            if (selfToggle.getValue()) disable();
            return;
        }

        Vec3 velocity = trackVelocity(target);

        OffhandModule offhand = Homovore.moduleManager.getModuleByClass(OffhandModule.class);
        if (offhand != null && offhand.shouldDeferForEat()) return;

        Vec3 anchor = target.position();

        double padding = reach.getValue() - mc.player.blockInteractionRange();

        Prediction prediction = predictFeet(target, anchor, velocity);
        boolean useElytraLock = validElytraLock(anchor, velocity, target.isFallFlying());
        if (lockedElytraFeet != null && !useElytraLock) clearElytraLock();
        boolean flightMode = target.isFallFlying() || useElytraLock;
        double targetSpeed = velocity.length();
        double wallThreshold = useElytraLock ? ELYTRA_IMPACT_SPEED : 0.1;
        boolean wallMode = target.isFallFlying() && targetSpeed >= wallThreshold;
        Vec3 desiredFeet = useElytraLock ? lockedElytraFeet : prediction.feet;
        Vec3 displacement = desiredFeet.subtract(anchor);
        Vec3 predFeet = prediction.feet;
        boolean complete = false;
        double chosenFraction = 0.0;
        int bestCoverage = -1;
        int bestSatisfied = -1;
        boolean bestLockable = false;
        boolean bestPlaceable = false;
        int selectedSatisfied = 0;
        Set<BlockPos> bestWanted = new HashSet<>();
        List<BlockPos> bestOrder = new ArrayList<>();
        List<BlockPos> bestScratch = new ArrayList<>();
        double[] backoff = useElytraLock
                ? LOCKED_CAGE_BACKOFF
                : flightMode ? ELYTRA_CAGE_BACKOFF : CAGE_BACKOFF;
        for (double fraction : backoff) {
            Vec3 candidateFeet = anchor.add(displacement.scale(fraction));
            boolean candidateComplete = wallMode
                    ? buildInterceptionWall(candidateFeet, target, velocity, padding)
                    : buildCage(candidateFeet, target, padding, flightMode);
            int candidateReachable = wanted.size();
            int candidateCoverage = candidateReachable + satisfiedCells;
            boolean candidateLockable = wallMode
                    && candidateReachable >= MIN_ELYTRA_LOCK_CELLS;
            boolean candidatePlaceable = candidateReachable > 0;
            if ((candidateLockable && !bestLockable)
                    || (candidateLockable == bestLockable && candidatePlaceable && !bestPlaceable)
                    || (candidateLockable == bestLockable && candidatePlaceable == bestPlaceable
                    && (candidateCoverage > bestCoverage
                    || (candidateCoverage == bestCoverage && satisfiedCells > bestSatisfied)))) {
                bestCoverage = candidateCoverage;
                bestSatisfied = satisfiedCells;
                bestLockable = candidateLockable;
                bestPlaceable = candidatePlaceable;
                selectedSatisfied = satisfiedCells;
                predFeet = candidateFeet;
                complete = candidateComplete;
                chosenFraction = fraction;
                bestWanted.clear();
                bestWanted.addAll(wanted);
                bestOrder.clear();
                bestOrder.addAll(order);
                bestScratch.clear();
                bestScratch.addAll(scratch);
            }
        }
        wanted.clear();
        wanted.addAll(bestWanted);
        order.clear();
        order.addAll(bestOrder);
        scratch.clear();
        scratch.addAll(bestScratch);
        int cageCells = scratch.size();
        int reachable = wanted.size();
        boolean createdElytraLock = wallMode
                && !useElytraLock
                && reachable >= MIN_ELYTRA_LOCK_CELLS;
        if (createdElytraLock) {
            lockedElytraFeet = predFeet;
            elytraLockTicks = ELYTRA_LOCK_TICKS;
        } else if (useElytraLock) {
            elytraLockTicks--;
        }
        if (flightMode && (useElytraLock || createdElytraLock)) {
            prioritizeElytraPlacements(predFeet, velocity);
        }
        boolean commit = reachable > 0
                && (!flightMode || useElytraLock || createdElytraLock);
        if (!commit) {
            wanted.clear();
            order.clear();
        }

        Homovore.placementManager.removeQueuedFor(p -> owned.contains(p) && !wanted.contains(p));
        owned.retainAll(wanted);
        sentAt.keySet().retainAll(wanted);
        sendAttempts.keySet().retainAll(wanted);

        int sentCount = 0;
        if (commit) {
            long now = System.currentTimeMillis();
            for (BlockPos pos : order) {
                Long last = sentAt.get(pos);
                if (last != null && now - last < RESEND_MS) continue;
                if (sendAttempts.getOrDefault(pos, 0) >= MAX_SEND_ATTEMPTS) {
                    if (last != null && now - last < RETRY_RESET_MS) continue;
                    sendAttempts.remove(pos);
                }
                if (Homovore.placementManager.enqueueExtendedReach(pos, slot)) {
                    owned.add(pos);
                    sentAt.put(pos, now);
                    sendAttempts.merge(pos, 1, Integer::sum);
                    sentCount++;
                }
            }
            if (sentCount > 0) Homovore.placementManager.flushQueue();
        }

        if (debug.getValue()) {
            Homovore.LOGGER.info(
                    "[AutoTrap] pose={} grounded={} elytra={} locked={} wall={} dist={} vel={} accel={} horizon={} fraction={} pred=[{}] tgt=[{}] cage={} solid={} reach={} complete={} sent={} queued={}",
                    target.getBbHeight() <= 1.0 ? "compact" : "upright",
                    target.onGround(),
                    target.isFallFlying(),
                    useElytraLock || createdElytraLock,
                    wallMode,
                    String.format("%.2f", Math.sqrt(mc.player.distanceToSqr(target))),
                    String.format("%.3f", velocity.length()),
                    String.format("%.3f", velocityChange.length()),
                    String.format("%.2f", prediction.horizon),
                    String.format("%.2f", chosenFraction),
                    fmt(predFeet),
                    fmt(target.position()),
                    cageCells,
                    selectedSatisfied,
                    reachable,
                    complete,
                    sentCount,
                    owned.size());
        }
    }

    private static String fmt(Vec3 v) {
        return String.format("%.1f,%.1f,%.1f", v.x, v.y, v.z);
    }

    private boolean buildCage(Vec3 feet, LivingEntity t, double padding, boolean forceCompact) {
        scratch.clear();
        if (forceCompact || t.getBbHeight() <= 1.0) compactCells(feet, t, scratch, forceCompact);
        else uprightCells(feet, t, scratch);

        return evaluateCells(padding, null);
    }

    private boolean buildInterceptionWall(Vec3 feet, LivingEntity target, Vec3 velocity, double padding) {
        scratch.clear();

        double halfWidth = target.getBbWidth() * 0.5;
        int minX = Mth.floor(feet.x - halfWidth);
        int maxX = Mth.floor(feet.x + halfWidth - 1.0E-6);
        int minY = Mth.floor(feet.y);
        int maxY = Mth.floor(feet.y + 0.6 - 1.0E-6);
        int minZ = Mth.floor(feet.z - halfWidth);
        int maxZ = Mth.floor(feet.z + halfWidth - 1.0E-6);

        double absX = Math.abs(velocity.x);
        double absY = Math.abs(velocity.y);
        double absZ = Math.abs(velocity.z);
        if (absY > absX && absY > absZ) {
            int y = velocity.y >= 0.0 ? minY : maxY;
            for (int x = minX; x <= maxX; x++)
                for (int z = minZ; z <= maxZ; z++)
                    scratch.add(new BlockPos(x, y, z));
        } else if (absX >= absZ) {
            int x = velocity.x >= 0.0 ? minX : maxX;
            for (int y = minY; y <= maxY; y++)
                for (int z = minZ; z <= maxZ; z++)
                    scratch.add(new BlockPos(x, y, z));
        } else {
            int z = velocity.z >= 0.0 ? minZ : maxZ;
            for (int x = minX; x <= maxX; x++)
                for (int y = minY; y <= maxY; y++)
                    scratch.add(new BlockPos(x, y, z));
        }

        AABB predictedBox = new AABB(
                feet.x - halfWidth, feet.y, feet.z - halfWidth,
                feet.x + halfWidth, feet.y + 0.6, feet.z + halfWidth);
        return evaluateCells(padding, predictedBox);
    }

    private boolean evaluateCells(double padding, AABB requiredCollision) {
        satisfiedCells = 0;
        wanted.clear();
        order.clear();
        boolean complete = true;
        for (BlockPos pos : scratch) {
            if (speedMineClaims(pos)) {
                complete = false;
                continue;
            }
            var state = mc.level.getBlockState(pos);
            if (!state.canBeReplaced()) {
                boolean blocksPath = state.getCollisionShape(mc.level, pos).toAabbs().stream()
                        .map(shape -> shape.move(pos.getX(), pos.getY(), pos.getZ()))
                        .anyMatch(shape -> requiredCollision == null || shape.intersects(requiredCollision));
                if (blocksPath) satisfiedCells++;
                else complete = false;
                continue;
            }
            if (mc.player.isWithinBlockInteractionRange(pos, padding) && canPlaceAtConfiguredReach(pos)) {
                if (wanted.add(pos)) order.add(pos);
            } else {
                complete = false;
            }
        }
        return complete && !order.isEmpty();
    }

    private boolean canPlaceAtConfiguredReach(BlockPos pos) {
        if (mc.level.isOutsideBuildHeight(pos)) return false;
        if (mc.player.getBoundingBox().intersects(new AABB(pos))) return false;
        return PlaceUtil.noEntityCollision(pos);
    }

    private boolean speedMineClaims(BlockPos pos) {
        SpeedMineModule mine = Homovore.moduleManager.getModuleByClass(SpeedMineModule.class);
        return mine != null && mine.isEnabled() && mine.alreadyBreaking(pos);
    }

    private boolean validElytraLock(Vec3 anchor, Vec3 velocity, boolean fallFlying) {
        if (lockedElytraFeet == null || elytraLockTicks <= 0) return false;
        if (!fallFlying) return anchor.distanceTo(lockedElytraFeet) <= 2.5;
        if (velocity.lengthSqr() < 0.01) return anchor.distanceTo(lockedElytraFeet) <= 2.5;
        Vec3 direction = velocity.normalize();
        Vec3 toLock = lockedElytraFeet.subtract(anchor);
        double forward = toLock.dot(direction);
        double lateral = toLock.subtract(direction.scale(forward)).length();
        return forward >= -0.25 && lateral <= 1.5;
    }

    private void prioritizeElytraPlacements(Vec3 feet, Vec3 velocity) {
        if (velocity.lengthSqr() < 0.01) return;
        Vec3 direction = velocity.normalize();
        order.sort(Comparator.comparingDouble(pos -> Vec3.atCenterOf(pos).subtract(feet).dot(direction)));
    }

    private void clearElytraLock() {
        lockedElytraFeet = null;
        elytraLockTicks = 0;
    }

    private void compactCells(Vec3 feet, LivingEntity t, List<BlockPos> out, boolean elytraShape) {
        double w = t.getBbWidth() * 0.5;
        int y = Mth.floor(feet.y + (elytraShape ? 0.3 : t.getBbHeight() * 0.5));
        int minX = Mth.floor(feet.x - w), maxX = Mth.floor(feet.x + w - 1.0E-6);
        int minZ = Mth.floor(feet.z - w), maxZ = Mth.floor(feet.z + w - 1.0E-6);
        for (int x = minX; x <= maxX; x++)
            for (int z = minZ; z <= maxZ; z++) {
                out.add(new BlockPos(x, y - 1, z));
                out.add(new BlockPos(x, y + 1, z));
            }
        for (int x = minX; x <= maxX; x++)
            for (int z = minZ; z <= maxZ; z++)
                for (Direction d : Direction.Plane.HORIZONTAL) {
                    int nx = x + d.getStepX(), nz = z + d.getStepZ();
                    if (nx >= minX && nx <= maxX && nz >= minZ && nz <= maxZ) continue;
                    out.add(new BlockPos(nx, y, nz));
                }
    }

    private void uprightCells(Vec3 feet, LivingEntity t, List<BlockPos> out) {
        double w = t.getBbWidth() * 0.5;
        int feetY = Mth.floor(feet.y);
        int headY = feetY + 1;
        int minX = Mth.floor(feet.x - w), maxX = Mth.floor(feet.x + w);
        int minZ = Mth.floor(feet.z - w), maxZ = Mth.floor(feet.z + w);

        if (!t.onGround()) {
            for (int x = minX; x <= maxX; x++)
                for (int z = minZ; z <= maxZ; z++)
                    out.add(new BlockPos(x, feetY - 1, z));
        }
        for (int x = minX; x <= maxX; x++)
            for (int z = minZ; z <= maxZ; z++)
                for (Direction d : Direction.Plane.HORIZONTAL) {
                    int nx = x + d.getStepX(), nz = z + d.getStepZ();
                    if (nx >= minX && nx <= maxX && nz >= minZ && nz <= maxZ) continue;
                    out.add(new BlockPos(nx, headY, nz));
                }
        for (int x = minX; x <= maxX; x++)
            for (int z = minZ; z <= maxZ; z++)
                out.add(new BlockPos(x, feetY + 2, z));
    }

    private void pruneAll() {
        if (!owned.isEmpty()) {
            Homovore.placementManager.removeQueuedFor(owned::contains);
            owned.clear();
        }
        wanted.clear();
        order.clear();
        sentAt.clear();
        sendAttempts.clear();
    }

    @Override
    public void onRender3D(Render3DEvent event) {
        if (!render.getValue() || wanted.isEmpty()) return;
        Color fc = fillColor.getValue();
        Color oc = outlineColor.getValue();
        float lw = lineWidth.getValue();
        for (BlockPos pos : wanted) {
            RenderUtil.drawBoxFilled(event.getMatrix(), pos, fc);
            RenderUtil.drawBox(event.getMatrix(), pos, oc, lw);
        }
    }

    private Vec3 trackVelocity(LivingEntity t) {
        Vec3 cur = t.position();
        if (!t.getUUID().equals(trackedId)) {
            trackedId = t.getUUID();
            prevPos = cur;
            filteredVelocity = Vec3.ZERO;
            velocityChange = Vec3.ZERO;
            return filteredVelocity;
        }

        Vec3 raw = cur.subtract(prevPos);
        prevPos = cur;
        if (raw.length() > MAX_SAMPLE_SPEED) {
            velocityChange = filteredVelocity.scale(-1.0);
            filteredVelocity = Vec3.ZERO;
            return filteredVelocity;
        }

        Vec3 previous = filteredVelocity;
        filteredVelocity = previous.scale(0.55).add(raw.scale(0.45));
        velocityChange = filteredVelocity.subtract(previous);
        return filteredVelocity;
    }

    private Prediction predictFeet(LivingEntity target, Vec3 anchor, Vec3 velocity) {
        double speed = velocity.length();
        if (speed < 0.01) return new Prediction(anchor, 0.0);

        double baseHorizon = target.onGround() ? 3.0 : target.isFallFlying() ? 2.25 : 2.0;
        double instability = velocityChange.length() / (speed + 0.05);
        double minimumHorizon = target.isFallFlying() ? 1.5 : 0.75;
        double horizon = Mth.clamp(baseHorizon / (1.0 + instability * 1.5), minimumHorizon, 3.0);

        double dx = velocity.x * horizon;
        double dz = velocity.z * horizon;
        double dy;
        if (target.onGround()) {
            dy = 0.0;
        } else if (target.isFallFlying()) {
            dy = velocity.y * horizon;
        } else {
            dy = velocity.y * horizon - 0.04 * horizon * horizon;
        }

        Vec3 displacement = new Vec3(dx, dy, dz);
        double maximumDistance = target.isFallFlying()
                ? MAX_ELYTRA_PREDICT_DISTANCE
                : MAX_PREDICT_DISTANCE;
        if (displacement.length() > maximumDistance) {
            displacement = displacement.normalize().scale(maximumDistance);
        }
        return new Prediction(clampToCollision(target, anchor, anchor.add(displacement)), horizon);
    }

    private Vec3 clampToCollision(LivingEntity target, Vec3 from, Vec3 to) {
        Vec3 delta = to.subtract(from);
        if (delta.lengthSqr() < 1.0E-6) return from;

        AABB startBox = target.getBoundingBox();
        Set<BlockPos> startingCollisions = collisionCells(startBox);

        int steps = Math.max(1, Mth.ceil(delta.length() / 0.25));
        Vec3 last = from;
        for (int step = 1; step <= steps; step++) {
            Vec3 sample = from.add(delta.scale(step / (double) steps));
            Set<BlockPos> collisions = collisionCells(startBox.move(sample.subtract(from)));
            if (collisions.stream().anyMatch(pos -> !startingCollisions.contains(pos))) break;
            last = sample;
        }
        return last;
    }

    private Set<BlockPos> collisionCells(AABB box) {
        Set<BlockPos> collisions = new HashSet<>();
        for (BlockPos raw : BlockPos.betweenClosed(
                Mth.floor(box.minX), Mth.floor(box.minY), Mth.floor(box.minZ),
                Mth.floor(box.maxX), Mth.floor(box.maxY), Mth.floor(box.maxZ))) {
            BlockPos pos = raw.immutable();
            if (mc.level.getBlockState(pos).getCollisionShape(mc.level, pos).toAabbs().stream()
                    .map(shape -> shape.move(pos.getX(), pos.getY(), pos.getZ()))
                    .anyMatch(shape -> shape.intersects(box))) {
                collisions.add(pos);
            }
        }
        return collisions;
    }

    private void resetTracking() {
        trackedId = null;
        prevPos = null;
        filteredVelocity = Vec3.ZERO;
        velocityChange = Vec3.ZERO;
        clearElytraLock();
    }

    private record Prediction(Vec3 feet, double horizon) {}

    private LivingEntity findTarget() {
        TargetsModule targets = Homovore.moduleManager.getModuleByClass(TargetsModule.class);
        double maxSq = range.getValue() * range.getValue();
        LivingEntity best = null;
        double bestSq = Double.MAX_VALUE;
        for (Player p : mc.level.players()) {
            if (p == mc.player) continue;
            if (targets != null && !targets.isValidPlayerTarget(p)) continue;
            double dSq = mc.player.distanceToSqr(p);
            if (dSq > maxSq || dSq >= bestSq) continue;
            bestSq = dSq;
            best = p;
        }
        return best;
    }

    private int resolveSlot() {
        var r = InventoryUtil.find(Items.OBSIDIAN, InventoryUtil.PLACE_SCOPE);
        return (r.found() && r.type() != ResultType.OFFHAND) ? r.slot() : -1;
    }
}
