/**
 * planner.js — планировщик маршрута.
 *
 * Только чистые функции: без DOM, сети и Date.now(). Одинаковый вход → одинаковый план.
 *
 * Форматы:
 *   точка   — объект { id, la, lo, ... } (la — широта, lo — долгота); планировщик её не меняет
 *             и возвращает те же объекты, что получил;
 *   узел    — массив [lat, lon];
 *   матрица — { km: number[][], min: number[][], est: boolean }, est=true — оценка «прямая × 1,3».
 */

export const ROAD_FACTOR = 1.3; // прямая × 1,3 — оценка длины по дорогам
export const V_CITY = 25;       // км/ч на коротких переездах (< 15 км)
export const V_ROAD = 65;       // км/ч на трассе

/** Координаты точки как узел [lat, lon]. */
export const ll = p => [p.la, p.lo];

/** Расстояние по прямой между узлами [lat, lon], км. */
export function haversine(a, b) {
  const R = 6371, r = Math.PI / 180;
  const dLat = (b[0] - a[0]) * r, dLon = (b[1] - a[1]) * r;
  const h = Math.sin(dLat / 2) ** 2 + Math.cos(a[0] * r) * Math.cos(b[0] * r) * Math.sin(dLon / 2) ** 2;
  return 2 * R * Math.asin(Math.sqrt(h));
}

/** Оценка времени в пути (мин) по длине отрезка (км). */
export const legMinutes = km => km / (km < 15 ? V_CITY : V_ROAD) * 60;

/** Оценочная матрица «прямая × 1,3» по узлам. */
export function estimateMatrix(nodes) {
  const n = nodes.length, km = [], min = [];
  for (let i = 0; i < n; i++) {
    km[i] = [];
    min[i] = [];
    for (let j = 0; j < n; j++) {
      const k = haversine(nodes[i], nodes[j]) * ROAD_FACTOR;
      km[i][j] = k;
      min[i][j] = legMinutes(k);
    }
  }
  return { km, min, est: true };
}

/**
 * Зоны: точки ближе radiusKm друг к другу попадают в одну зону (цепочкой: A~B, B~C → A, B, C вместе).
 * Возвращает массив зон, зона — массив точек.
 * С шага 2 buildPlan её не использует (дни собираются groupByProximity).
 */
export function makeZones(points, radiusKm) {
  const n = points.length, parent = [...Array(n).keys()];
  const find = i => (parent[i] === i ? i : (parent[i] = find(parent[i])));
  for (let i = 0; i < n; i++)
    for (let j = i + 1; j < n; j++)
      if (haversine(ll(points[i]), ll(points[j])) < radiusKm) parent[find(i)] = find(j);
  const groups = {};
  points.forEach((p, i) => {
    const k = find(i);
    (groups[k] = groups[k] || []).push(p);
  });
  return Object.values(groups);
}

/**
 * Порядок групп точек (зон или дней) от старта. Стоимость перехода — кратчайшее расстояние между группами.
 * До 8 зон — перебор всех вариантов, больше — «ближайшая следующая» + 2-opt.
 */
export function orderZones(zones, start) {
  const n = zones.length;
  if (n < 2) return zones;
  const gap = (A, B) => {
    let m = 1e9;
    for (const a of A) for (const b of B) {
      const d = haversine(ll(a), ll(b));
      if (d < m) m = d;
    }
    return m;
  };
  const fromStart = zones.map(z => Math.min(...z.map(p => haversine(start, ll(p)))));
  const G = zones.map(a => zones.map(b => (a === b ? 0 : gap(a, b))));
  const cost = o => o.reduce((s, z, i) => s + (i ? G[o[i - 1]][z] : fromStart[z]), 0);

  let best = null, bestCost = Infinity;
  if (n <= 8) {
    const perm = (arr, l) => {
      if (l === arr.length) {
        const v = cost(arr);
        if (v < bestCost) { bestCost = v; best = arr.slice(); }
        return;
      }
      for (let i = l; i < arr.length; i++) {
        [arr[l], arr[i]] = [arr[i], arr[l]];
        perm(arr, l + 1);
        [arr[l], arr[i]] = [arr[i], arr[l]];
      }
    };
    perm([...Array(n).keys()], 0);
  } else {
    // ближайшая следующая
    const rest = [...Array(n).keys()], o = [];
    let cur = -1;
    while (rest.length) {
      let bi = 0;
      rest.forEach((z, i) => {
        const c = cur < 0 ? fromStart[z] : G[cur][z];
        const cb = cur < 0 ? fromStart[rest[bi]] : G[cur][rest[bi]];
        if (c < cb) bi = i;
      });
      cur = rest.splice(bi, 1)[0];
      o.push(cur);
    }
    // 2-opt
    bestCost = cost(o);
    let improved = true;
    while (improved) {
      improved = false;
      for (let i = 0; i < n - 1; i++)
        for (let k = i + 1; k < n; k++) {
          const c = o.slice(0, i).concat(o.slice(i, k + 1).reverse(), o.slice(k + 1));
          const v = cost(c);
          if (v < bestCost - 1e-9) { o.splice(0, n, ...c); bestCost = v; improved = true; }
        }
    }
    best = o;
  }
  return best.map(i => zones[i]);
}

/**
 * Обход узлов 0..n-1 по матрице времени, начиная с узла 0:
 * «ближайшая следующая» → 2-opt → Or-opt (перенос одной точки), до 40 кругов улучшений.
 * end — индекс узла, в который нужно вернуться в конце (учитывается в стоимости), или null.
 * Возвращает порядок узлов без начального 0.
 */
export function tour(M, n, end = null) {
  const cost = (a, b) => M.min[a][b];
  const rest = [];
  for (let i = 1; i < n; i++) rest.push(i);
  const path = [0];
  while (rest.length) {
    const last = path[path.length - 1];
    let bi = 0;
    rest.forEach((x, i) => { if (cost(last, x) < cost(last, rest[bi])) bi = i; });
    path.push(rest.splice(bi, 1)[0]);
  }
  const pathCost = p => {
    let s = 0;
    for (let i = 1; i < p.length; i++) s += cost(p[i - 1], p[i]);
    return end != null ? s + cost(p[p.length - 1], end) : s;
  };

  let best = pathCost(path), improved = true, rounds = 0;
  while (improved && rounds++ < 40) {
    improved = false;
    // 2-opt: разворот отрезка
    for (let i = 1; i < path.length - 1; i++)
      for (let k = i + 1; k < path.length; k++) {
        const c = path.slice(0, i).concat(path.slice(i, k + 1).reverse(), path.slice(k + 1));
        const v = pathCost(c);
        if (v < best - 1e-9) { path.splice(0, path.length, ...c); best = v; improved = true; }
      }
    // Or-opt: перенос одной точки на другое место
    for (let i = 1; i < path.length; i++)
      for (let j = 1; j < path.length; j++) {
        if (i === j) continue;
        const c = path.slice();
        const x = c.splice(i, 1)[0];
        c.splice(j, 0, x);
        const v = pathCost(c);
        if (v < best - 1e-9) { path.splice(0, path.length, ...c); best = v; improved = true; }
      }
  }
  return path.slice(1);
}

/** Узлы для матрицы: [откуда, ...точки] и старт в конце, если нужно вернуться. */
export function zoneNodes(from, zone, backTo = null) {
  const nodes = [from, ...zone.map(ll)];
  if (backTo) nodes.push(backTo);
  return nodes;
}

/** Подматрица по списку индексов узлов. */
export function subMatrix(M, idx) {
  return {
    km: idx.map(i => idx.map(j => M.km[i][j])),
    min: idx.map(i => idx.map(j => M.min[i][j])),
    est: M.est,
  };
}

/**
 * Очерёдность точек по готовой матрице M (построена по zoneNodes).
 * back — в конце вернуться в последний узел матрицы (старт).
 * Возвращает { pts, legs, ret }: точки по порядку, отрезок до каждой точки, возврат на старт или null.
 */
export function routeZone(zone, M, back = false) {
  const n = zone.length + 1;
  const end = back ? n : null;
  const ord = tour(M, n, end);
  const legs = ord.map((i, k) => {
    const from = k ? ord[k - 1] : 0;
    return { km: M.km[from][i], min: M.min[from][i] };
  });
  const last = ord[ord.length - 1];
  return {
    pts: ord.map(i => zone[i - 1]),
    legs,
    ret: back ? { km: M.km[last][end], min: M.min[last][end] } : null,
  };
}

const isBase = cfg => cfg.mode !== 'stay';
const maxPerDay = cfg => (cfg.max > 0 ? cfg.max : Infinity);

/**
 * Оценка длительности дня, мин: езда по оценочной матрице + cfg.stop минут на точке.
 * Режим «из старта» (cfg.mode !== 'stay') — с дорогой от старта и обратно.
 */
export function estimateDayMinutes(pts, cfg, start) {
  const base = isBase(cfg);
  const nodes = base ? [start, ...pts.map(ll)] : pts.map(ll);
  if (!nodes.length) return 0;
  const M = estimateMatrix(nodes);
  const ord = tour(M, nodes.length, base ? 0 : null);
  let s = 0, prev = 0;
  for (const i of ord) { s += M.min[prev][i]; prev = i; }
  if (base) s += M.min[prev][0];
  return s + cfg.stop * pts.length;
}

/** Детерминированный генератор случайных чисел (mulberry32) — для фиксированного seed. */
function rng(seed) {
  let s = seed | 0;
  return () => {
    s = (s + 0x6D2B79F5) | 0;
    let t = Math.imul(s ^ (s >>> 15), 1 | s);
    t = (t + Math.imul(t ^ (t >>> 7), 61 | t)) ^ t;
    return ((t ^ (t >>> 14)) >>> 0) / 4294967296;
  };
}

/**
 * Сбалансированный k-means: делит точки на k компактных групп, в каждой не больше ceil(n/k) точек.
 * Начальные центры — k-means++ на генераторе с фиксированным seed, лучший из restarts запусков.
 * Одинаковый вход → одинаковые группы. Возвращает непустые группы (массивы точек).
 */
export function balancedKMeans(points, k, seed = 1, restarts = 8) {
  const X = points.map(ll), n = X.length;
  if (k <= 1 || n <= 1) return [points.slice()];
  if (k >= n) return points.map(p => [p]);
  const cap = Math.ceil(n / k), rand = rng(seed);
  let best = null, bestCost = Infinity;
  for (let r = 0; r < restarts; r++) {
    // k-means++
    const C = [X[Math.floor(rand() * n)]];
    while (C.length < k) {
      const d = X.map(x => Math.min(...C.map(c => haversine(x, c))) ** 2);
      let s = d.reduce((a, b) => a + b, 0) * rand(), i = 0;
      while (i < n - 1 && (s -= d[i]) > 0) i++;
      C.push(X[i]);
    }
    let lab = null;
    for (let it = 0; it < 50; it++) {
      // назначение с ограничением размера: сначала самые близкие пары «точка — центр»
      const pairs = [];
      X.forEach((x, i) => C.forEach((c, j) => pairs.push([haversine(x, c), i, j])));
      pairs.sort((a, b) => a[0] - b[0] || a[1] - b[1] || a[2] - b[2]);
      const nl = Array(n).fill(-1), size = Array(k).fill(0);
      for (const [, i, j] of pairs) if (nl[i] < 0 && size[j] < cap) { nl[i] = j; size[j]++; }
      const same = lab && nl.every((v, i) => v === lab[i]);
      lab = nl;
      for (let j = 0; j < k; j++) {
        const m = X.filter((_, i) => lab[i] === j);
        if (m.length) C[j] = [m.reduce((a, x) => a + x[0], 0) / m.length, m.reduce((a, x) => a + x[1], 0) / m.length];
      }
      if (same) break;
    }
    const cost = X.reduce((s, x, i) => s + haversine(x, C[lab[i]]) ** 2, 0);
    if (cost < bestCost) { bestCost = cost; best = lab; }
  }
  return Array.from({ length: k }, (_, j) => points.filter((_, i) => best[i] === j)).filter(g => g.length);
}

/**
 * Объединение групп «самые близкие первыми» (близость — расстояние между самыми дальними точками).
 * Пара объединяется, только если объединённая группа не шире width и fits(точки) === true.
 * Если с одной из частей объединить было нельзя, с целой группой — тоже.
 */
function mergeClosest(groups, width, fits) {
  const n = groups.length, alive = Array(n).fill(true), members = groups.map(g => g.slice());
  const far = (A, B) => {
    let m = 0;
    for (const a of A) for (const b of B) m = Math.max(m, haversine(ll(a), ll(b)));
    return m;
  };
  const D = groups.map(a => groups.map(b => far(a, b)));
  const blocked = groups.map(() => Array(n).fill(false));
  for (;;) {
    let bi = -1, bj = -1, bd = Infinity;
    for (let i = 0; i < n; i++) {
      if (!alive[i]) continue;
      for (let j = i + 1; j < n; j++)
        if (alive[j] && !blocked[i][j] && D[i][j] < bd) { bd = D[i][j]; bi = i; bj = j; }
    }
    // ближайшая пара уже шире дня — остальные тем более
    if (bi < 0 || bd > width) break;
    const merged = members[bi].concat(members[bj]);
    if (fits(merged)) {
      members[bi] = merged;
      alive[bj] = false;
      for (let k = 0; k < n; k++) {
        if (!alive[k] || k === bi) continue;
        D[bi][k] = D[k][bi] = Math.max(D[bi][k], D[bj][k]);
        blocked[bi][k] = blocked[k][bi] = blocked[bi][k] || blocked[bj][k];
      }
    } else {
      blocked[bi][bj] = blocked[bj][bi] = true;
    }
  }
  return members.filter((_, i) => alive[i]);
}

/**
 * Дни по близости — размер дня получается из расположения точек, а не из заданного числа:
 *   1. скопления: объединяем самые близкие точки, пока скопление не шире cfg.width км;
 *   2. скопление, которое не влезает в один день (cfg.hours, cfg.max), делим на минимальное число
 *      компактных частей сбалансированным k-means;
 *   3. соседние части объединяем «самые близкие первыми», если день не шире cfg.width и влезает.
 * «Влезает»: не больше cfg.max точек (если cfg.max > 0) и оценка езды + стоянок ≤ cfg.hours
 * (в режиме «из старта» — с дорогой от старта и обратно).
 * Возвращает массив групп (массивы точек) в исходном порядке точек внутри группы.
 */
export function groupByProximity(points, cfg, start) {
  const limit = cfg.hours * 60, max = maxPerDay(cfg);
  const width = cfg.width > 0 ? cfg.width : Infinity;
  const order = new Map(points.map((p, i) => [p, i]));
  const sorted = g => g.slice().sort((a, b) => order.get(a) - order.get(b));
  const fits = g => g.length <= max && estimateDayMinutes(sorted(g), cfg, start) <= limit;

  const clusters = mergeClosest(points.map(p => [p]), width, () => true).map(sorted);
  const parts = [];
  for (const c of clusters) {
    if (fits(c)) { parts.push(c); continue; }
    for (let k = Math.max(2, Math.ceil(c.length / max)); ; k++) {
      const split = balancedKMeans(c, k);
      if (k >= c.length || split.every(fits)) { parts.push(...split); break; }
    }
  }
  return mergeClosest(parts, width, fits).map(sorted);
}

/**
 * Режим «ночёвка на месте»: день начинается там, где закончился предыдущий.
 * M — по узлам [откуда, ...группа] (+ старт, если back). Не влезло по часам или числу — хвост в следующий день.
 */
function stayDays(group, M, cfg, from, back) {
  const r = routeZone(group, M, back), limit = cfg.hours * 60, max = maxPerDay(cfg);
  const days = [];
  let day = null, loc = from;
  r.pts.forEach((p, k) => {
    const leg = r.legs[k];
    if (!day || day.pts.length >= max || day.drive + day.stopM + leg.min + cfg.stop > limit) {
      day = { from: loc, pts: [], km: 0, drive: 0, stopM: 0 };
      days.push(day);
    }
    day.pts.push(p);
    day.km += leg.km;
    day.drive += leg.min;
    day.stopM += cfg.stop;
    loc = ll(p);
  });
  if (r.ret && day) {
    day.km += r.ret.km;
    day.drive += r.ret.min;
    day.ret = r.ret;
  }
  return days;
}

/**
 * Режим «каждый день из старта»: старт → точки → старт.
 * M — по узлам [старт, ...группа, старт]. Не влезло (с дорогой обратно) — остаток отдельным днём от старта.
 */
function baseDays(group, M, cfg, start) {
  const limit = cfg.hours * 60, max = maxPerDay(cfg), end = group.length + 1;
  const days = [];
  let rest = group.map((_, i) => i + 1); // индексы точек в M
  while (rest.length) {
    const sEnd = rest.length + 1, S = subMatrix(M, [0, ...rest, end]);
    const ord = tour(S, sEnd, sEnd);
    let prev = 0, km = 0, drive = 0, stopM = 0, cut = ord.length;
    for (let t = 0; t < ord.length; t++) {
      const i = ord[t];
      if (t > 0 && (t >= max || drive + S.min[prev][i] + stopM + cfg.stop + S.min[i][sEnd] > limit)) { cut = t; break; }
      km += S.km[prev][i];
      drive += S.min[prev][i];
      stopM += cfg.stop;
      prev = i;
    }
    const ret = { km: S.km[prev][sEnd], min: S.min[prev][sEnd] };
    days.push({
      from: start,
      pts: ord.slice(0, cut).map(i => group[rest[i - 1] - 1]),
      km: km + ret.km,
      drive: drive + ret.min,
      stopM,
      ret,
    });
    rest = ord.slice(cut).map(i => rest[i - 1]);
  }
  return days;
}

/**
 * Полный план: дни по близости → порядок дней → очерёдность внутри дня по матрице.
 *
 * points    — точки для маршрута (уже отфильтрованные);
 * cfg       — { mode: 'base'|'stay', width, hours, max, stop, loop };
 *             base — каждый день из старта и обратно; stay — ночёвка на месте (loop — вернуться в конце поездки);
 * start     — узел старта [lat, lon] или null (тогда старт — первая точка);
 * getMatrix — функция nodes → матрица (или Promise матрицы); вызывается один раз на группу дня.
 *             Планировщик сам в сеть не ходит: OSRM или оценку подставляет вызывающий.
 *
 * Возвращает { days, start, real, partial }. День: { from, pts, km, drive, stopM, ret?, group }.
 *   real    — все матрицы реальные (est=false); partial — часть реальные, часть оценочные.
 */
export async function buildPlan(points, cfg, start, getMatrix) {
  if (!points.length) return { days: [], start, real: false, partial: false };
  const start0 = start || ll(points[0]);
  const base = isBase(cfg);
  const groups = orderZones(groupByProximity(points, cfg, start0), start0);
  const days = [];
  let from = start0, real = 0;
  for (let gi = 0; gi < groups.length; gi++) {
    const g = groups[gi];
    const back = base || (!!cfg.loop && gi === groups.length - 1);
    const M = await getMatrix(zoneNodes(from, g, back ? start0 : null));
    if (!M.est) real++;
    const gd = base ? baseDays(g, M, cfg, start0) : stayDays(g, M, cfg, from, back);
    gd.forEach(d => { d.group = gi; days.push(d); });
    if (!base) {
      const last = gd[gd.length - 1];
      from = ll(last.pts[last.pts.length - 1]);
    }
  }
  return {
    days,
    start: start0,
    real: real === groups.length,
    partial: real > 0 && real < groups.length,
  };
}

/**
 * «Пересчитать остаток»: оставшиеся точки дня (rest) заново по порядку от текущего места from.
 * M — по узлам zoneNodes(from, rest, back ? старт : null). Остальные точки дня (посещённые) остаются впереди.
 * Возвращает новый день: skip — сколько точек в начале уже пройдено; km, drive, stopM — только остаток.
 */
export function rerouteDay(day, rest, from, M, back, stop) {
  const done = day.pts.filter(p => !rest.includes(p));
  if (!rest.length) return { ...day, pts: done, skip: done.length, km: 0, drive: 0, stopM: 0 };
  const r = routeZone(rest, M, back);
  let km = 0, drive = 0;
  for (const l of r.legs) { km += l.km; drive += l.min; }
  const out = { from, pts: [...done, ...r.pts], skip: done.length, km, drive, stopM: stop * rest.length, group: day.group };
  if (r.ret) {
    out.km += r.ret.km;
    out.drive += r.ret.min;
    out.ret = r.ret;
  }
  return out;
}

/* ---------- ручная правка ---------- */

const sameNode = (a, b) => !!a && !!b && a[0] === b[0] && a[1] === b[1];
const lastNode = day => ll(day.pts[day.pts.length - 1]);

/**
 * Перенос точки в другой день (toDay — индекс дня). Ничего не считает, только перекладывает.
 * Опустевший день удаляется. Возвращает { plan, changed }: новый план (исходный не меняется)
 * и индексы изменённых дней в нумерации нового плана.
 */
export function movePoint(plan, point, toDay) {
  const from = plan.days.findIndex(d => d.pts.includes(point));
  if (from < 0 || from === toDay || toDay < 0 || toDay >= plan.days.length) return { plan, changed: [] };
  const days = plan.days.map((d, i) => {
    if (i === from) return { ...d, pts: d.pts.filter(p => p !== point) };
    if (i === toDay) return { ...d, pts: [...d.pts, point] };
    return d;
  });
  let changed = [from, toDay];
  if (!days[from].pts.length) {
    days.splice(from, 1);
    changed = [toDay > from ? toDay - 1 : toDay];
  }
  return { plan: { ...plan, days }, changed };
}

/**
 * Порядок дня с закреплённым началом: узлы M — [откуда, ...fixed, ...rest] (+ старт, если back).
 * fixed (посещённые) идут первыми в своём порядке, rest упорядочивается от последней из них.
 */
function routeWithPrefix(day, fixed, rest, M, back, stop, from) {
  const f = fixed.length, r = rest.length, end = f + r + 1, list = [...fixed, ...rest];
  const idx = [f, ...rest.map((_, k) => f + 1 + k), ...(back ? [end] : [])];
  const ord = tour(subMatrix(M, idx), r + 1, back ? r + 1 : null).map(i => idx[i]);
  const seq = [...fixed.map((_, k) => k + 1), ...ord];
  let km = 0, drive = 0, prev = 0;
  for (const i of seq) { km += M.km[prev][i]; drive += M.min[prev][i]; prev = i; }
  const out = { from, pts: seq.map(i => list[i - 1]), km, drive, stopM: stop * list.length, group: day.group };
  if (back) {
    out.ret = { km: M.km[prev][end], min: M.min[prev][end] };
    out.km += out.ret.km;
    out.drive += out.ret.min;
  }
  return out;
}

/**
 * Пересчёт дней после ручной правки (например, movePoint).
 * changed — индексы изменённых дней. В режиме «ночёвка» пересчитывается и день, у которого сдвинулось
 * начало (последняя точка предыдущего дня) или сменилась необходимость вернуться на старт (cfg.loop).
 * Посещённые точки (isFixed) остаются впереди в своём порядке, остальные упорядочиваются заново.
 * День после «Пересчитать остаток» (skip) по-прежнему считается от того места.
 * getMatrix вызывается один раз на пересчитанный день. Перегруженный день не делится — это решение человека.
 * Возвращает { plan, touched }: новый план и индексы пересчитанных дней.
 */
export async function replanDays(plan, changed, cfg, getMatrix, isFixed = p => !!p.v) {
  const base = isBase(cfg), days = plan.days.slice(), touched = [];
  let anyReal = false, anyEst = false;
  for (let i = 0; i < days.length; i++) {
    const d = days[i], rerouted = d.skip != null;
    const from = base || rerouted ? d.from : i ? lastNode(days[i - 1]) : plan.start;
    const back = base || (!!cfg.loop && i === days.length - 1);
    if (!changed.includes(i) && sameNode(from, d.from) && !!d.ret === back) continue;
    const fixed = rerouted ? [] : d.pts.filter(isFixed);
    const rest = d.pts.filter(p => !fixed.includes(p) && !(rerouted && isFixed(p)));
    const M = await getMatrix(zoneNodes(from, [...fixed, ...rest], back ? plan.start : null));
    if (M.est) anyEst = true; else anyReal = true;
    days[i] = rerouted
      ? rerouteDay(d, rest, from, M, back, cfg.stop)
      : routeWithPrefix(d, fixed, rest, M, back, cfg.stop, from);
    touched.push(i);
  }
  const real = plan.real && !anyEst;
  return {
    plan: { ...plan, days, real, partial: !real && (plan.real || plan.partial || anyReal) },
    touched,
  };
}
