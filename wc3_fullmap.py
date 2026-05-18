import pymem, pymem.process, pymem.exception, pymem.pattern
import tkinter as tk
from tkinter import font
import keyboard, psutil, threading, time, struct

# ==============================================================
# 配置区
# ==============================================================
WAR3_PROCESS_NAMES  = ["warcraft iii.exe", "war3.exe", "frozen throne.exe"]
DEFAULT_REFRESH_HOTKEY = 'f5'

POINTER_CHAINS = {
    "普通资源": (0x00BE40A4, [0x4, 0x20C, 0x7C, 0x40, 0x88, 0x100]),
    "稀有资源": (0x00BE40A4, [0x4, 0xC, 0x178]),
    "感染度":   (0x00BB80D8, [0x1C, 0x864]),
    # ⭐ 饱食度已被删除，全权交由星链动态盲搜引擎接管
}
NUM_PLAYERS        = 5
SCAN_INTERVAL      = 0.05
UI_REFRESH_MS      = 200
NORMAL_FILTER      = 40
RARE_FILTER        = 20
ADDR_CACHE_TTL     = 20
REFUND_WINDOW_SEC  = 300
DEFAULT_FOOD       = 65   # 空槽位的默认饱食度（用于活跃检测）

# 反查触发阈值（连续失败次数；20Hz 下 30 ≈ 1.5 秒）
DISCOVER_FAIL_THRESHOLD = 30


# ==============================================================
# 📊 资源追踪器（纯检测，无硬编码槽位）
# ==============================================================
class ResourceTracker:
    def __init__(self, n=NUM_PLAYERS):
        self.n = n
        self._lock      = threading.Lock()
        self._prev      = [(None, None, None)] * n
        self.cum_normal = [0] * n
        self.cum_rare   = [0] * n
        self.cum_food   = [0] * n
        self._refund_n  = [[] for _ in range(n)]
        self._refund_r  = [[] for _ in range(n)]

        # ⭐ 完全无硬编码 - 全部由饱食度检测填充
        self.active_slots   = set()
        self._sorted_active = []   # 缓存排序结果，避免重复 sort

    def mark_food(self, slot_idx: int, food):
        """饱食度偏离默认值且在合法存活区间才标记为活跃；一旦活跃永久保留"""
        # ⚠️ 防御：拦截 16 万的乱码或负数，防止幽灵槽位激活
        if food is None or food <= 0 or food > 500 or food == DEFAULT_FOOD:
            return
        with self._lock:
            if slot_idx not in self.active_slots:
                self.active_slots.add(slot_idx)
                self._sorted_active = sorted(self.active_slots)

    def slot_to_res_idx(self, slot_idx: int):
        """槽位 → 密集资源数组索引；非活跃返回 None"""
        with self._lock:
            try:
                return self._sorted_active.index(slot_idx)
            except ValueError:
                return None

    def active_count(self) -> int:
        with self._lock:
            return len(self.active_slots)

    def _try_match_refund(self, queue: list, amount: int) -> bool:
        now = time.time()
        while queue and now - queue[0][0] > REFUND_WINDOW_SEC:
            queue.pop(0)
        for i in range(len(queue) - 1, -1, -1):
            if queue[i][1] == amount:
                queue.pop(i)
                return True
        return False

    def update(self, idx: int, normal=None, rare=None, food=None):
        prev_n, prev_r, prev_f = self._prev[idx]
        now = time.time()

        with self._lock:
            new_n, new_r, new_f = prev_n, prev_r, prev_f

            if normal is not None:
                if prev_n is not None:
                    dn = normal - prev_n
                    if dn < 0:
                        self._refund_n[idx].append((now, -dn))
                    elif dn > 0:
                        if self._try_match_refund(self._refund_n[idx], dn):
                            pass
                        elif dn % NORMAL_FILTER != 0:
                            self.cum_normal[idx] += dn
                new_n = normal

            if rare is not None:
                if prev_r is not None:
                    dr = rare - prev_r
                    if dr < 0:
                        self._refund_r[idx].append((now, -dr))
                    elif dr > 0:
                        if self._try_match_refund(self._refund_r[idx], dr):
                            pass
                        elif dr % RARE_FILTER != 0:
                            self.cum_rare[idx] += dr
                new_r = rare

            if food is not None:
                if prev_f is not None:
                    df = food - prev_f
                    if df > 0:
                        self.cum_food[idx] += df
                new_f = food

            self._prev[idx] = (new_n, new_r, new_f)

    def get(self, idx: int):
        with self._lock:
            return (self.cum_normal[idx],
                    self.cum_rare[idx],
                    self.cum_food[idx])

    def reset(self):
        with self._lock:
            self._prev      = [(None, None, None)] * self.n
            self.cum_normal = [0] * self.n
            self.cum_rare   = [0] * self.n
            self.cum_food   = [0] * self.n
            self._refund_n  = [[] for _ in range(self.n)]
            self._refund_r  = [[] for _ in range(self.n)]
            self.active_slots   = set()
            self._sorted_active = []


# ==============================================================
# 进程探测
# ==============================================================
def find_war3_pids():
    out = []
    for p in psutil.process_iter(['pid', 'name', 'memory_info']):
        try:
            nm = (p.info['name'] or '').lower()
            if any(t in nm for t in WAR3_PROCESS_NAMES):
                out.append((p.info['pid'],
                             p.info['memory_info'].rss / 1048576,
                             p.info['name']))
        except: pass
    return sorted(out, key=lambda x: x[1], reverse=True)


# ==============================================================
# 主界面
# ==============================================================
class War3StatsApp:
    def __init__(self, root):
        self.root = root
        self.root.title("避难所3统计面板")
        self.root.geometry("520x560")
        self.root.resizable(False, False)
        self.root.attributes("-topmost", True)

        self.pm            = None
        self.game_base     = None

        self.refresh_hotkey = DEFAULT_REFRESH_HOTKEY

        self.tracker = ResourceTracker()

        self._scan_lock = threading.Lock()
        self._scan_data = [
            dict(valid=False,
                 live_n=None, live_r=None, live_f=None, live_i=None,
                 cum_n=0,  cum_r=0,  cum_f=0,
                 is_active=False)
            for _ in range(NUM_PLAYERS)
        ]

        self._addr_cache   = None
        self._cache_countdown = 0
        self._food_offset_from_inf = None # ⭐ 星链计划：动态记录物理距离

        # ⭐ 自动反查相关
        self.player_blocks      = {}    # {slot: normal_resource_addr}
        self._discover_running  = False
        self._slot_fail_count   = [0] * NUM_PLAYERS
        self._discover_attempts = 0      # 总尝试次数，避免无限重试
        self._discover_failed   = False  # 标记反查已失败（避免反复尝试）
        # ⭐ 卡死检测
        self._resource_stable_count = [0] * NUM_PLAYERS
        self._prev_resource = [None] * NUM_PLAYERS
        self._initial_discovered = False
        # ⭐ 记录上次反查时的活跃集合（活跃变大就重查）
        self._last_discover_active = None

        self.init_ui()
        self._register_hotkeys()

        threading.Thread(target=self._watchdog,  daemon=True).start()
        threading.Thread(target=self._scanner,   daemon=True).start()

        self.root.after(UI_REFRESH_MS, self._ui_tick)
        self.root.after(100, self.manual_refresh)

    def init_ui(self):
        fh   = font.Font(family="微软雅黑", size=14, weight="bold")
        self.f_btn = font.Font(family="微软雅黑", size=11)
        ft   = font.Font(family="微软雅黑", size=9)
        fm   = font.Font(family="Consolas",  size=9)
        fa   = font.Font(family="Consolas",  size=8,  slant="italic")

        tk.Label(self.root, text="避难所3统计面板", font=fh).pack(pady=8)

        fr = tk.Frame(self.root); fr.pack(pady=3)
        self.lbl_status = tk.Label(fr, text="等待游戏...", fg="red",
                                   font=ft, width=20, anchor='w')
        self.lbl_status.pack(side=tk.LEFT, padx=2)
        self.btn_refresh = tk.Button(fr,
            text=f"↻ 刷新 ({self.refresh_hotkey.upper()})",
            font=("微软雅黑", 9), width=14, bg="#e0e0e0",
            command=self.manual_refresh)
        self.btn_refresh.pack(side=tk.LEFT, padx=2)
        tk.Button(fr, text="改键", font=("微软雅黑", 9), width=4, bg="#e0e0e0",
                  command=self.change_key).pack(side=tk.LEFT)

        tk.Label(self.root,
                 text="纯只读统计 · 不修改任何游戏数据",
                 fg="#888", font=ft).pack(pady=(4, 0))

        panel = tk.LabelFrame(self.root,
            text=" 📡 全图经济雷达  [自动识别+反查] ",
            font=self.f_btn, fg="#006400")
        panel.pack(pady=6, fill="x", padx=12)

        self.lbl_detect = tk.Label(panel,
            text="正在等待玩家活动以识别活跃槽位...",
            font=("微软雅黑", 8), fg="#888")
        self.lbl_detect.pack(pady=(2, 0))

        hdr = tk.Frame(panel); hdr.pack(fill="x", padx=6, pady=(4,0))
        for txt, w in [("槽位",8),("普通",7),("稀有",6),("饱食",6),("感染",6)]:
            tk.Label(hdr, text=txt, font=fm, width=w,
                     anchor="e" if txt!="槽位" else "w",
                     fg="#555").pack(side=tk.LEFT)
        tk.Frame(panel, height=1, bg="#ccc").pack(fill="x", padx=6)

        self.row_labels = []
        for i in range(NUM_PLAYERS):
            tag = f"P{i+1}"

            fl = tk.Frame(panel); fl.pack(fill="x", padx=6, pady=(3,0))
            lbl_tag_live = tk.Label(fl, text=f"{tag} 实时",
                                    font=fm, width=8, anchor="w")
            lbl_tag_live.pack(side=tk.LEFT)
            ln = tk.Label(fl, text="---", font=fm, width=7, anchor="e")
            ln.pack(side=tk.LEFT)
            lr = tk.Label(fl, text="---", font=fm, width=6, anchor="e")
            lr.pack(side=tk.LEFT)
            lf = tk.Label(fl, text="---", font=fm, width=6, anchor="e")
            lf.pack(side=tk.LEFT)
            li = tk.Label(fl, text="---", font=fm, width=6, anchor="e", fg="red")
            li.pack(side=tk.LEFT)

            fc = tk.Frame(panel); fc.pack(fill="x", padx=6, pady=(0,3))
            lbl_tag_cum = tk.Label(fc, text="  ↑累计",
                                   font=fm, width=8, anchor="w", fg="#3a7d3a")
            lbl_tag_cum.pack(side=tk.LEFT)
            cn = tk.Label(fc, text="+0", font=fm, width=7, anchor="e", fg="#3a7d3a")
            cn.pack(side=tk.LEFT)
            cr = tk.Label(fc, text="+0", font=fm, width=6, anchor="e", fg="#3a7d3a")
            cr.pack(side=tk.LEFT)
            cf = tk.Label(fc, text="+0", font=fm, width=6, anchor="e", fg="#3a7d3a")
            cf.pack(side=tk.LEFT)
            tk.Label(fc, text="", width=6).pack(side=tk.LEFT)

            if i < NUM_PLAYERS-1:
                tk.Frame(panel, height=1, bg="#ddd").pack(fill="x", padx=6)

            self.row_labels.append(dict(
                fl=fl, fc=fc,
                tag_live=lbl_tag_live, tag_cum=lbl_tag_cum,
                ln=ln, lr=lr, lf=lf, li=li,
                cn=cn, cr=cr, cf=cf,
            ))

        tk.Button(panel, text="🔄 重置累计", font=("微软雅黑",9),
                  bg="#ffdada", command=self._reset_tracker).pack(pady=4)

        tk.Label(self.root, text="©By 秒杀再重生",
                 font=fa, fg="#FF8C00").place(relx=0.98, rely=0.99, anchor="se")

    def _ui_tick(self):
        with self._scan_lock:
            snapshot = [d.copy() for d in self._scan_data]

        def fmt(v):
            return f"{v:,}" if v is not None else "---"

        active_count = self.tracker.active_count()
        discovered = len([s for s in self.player_blocks if s != 0])

        if self._discover_running:
            self.lbl_detect.config(
                text="🔍 正在反查玩家资源地址（约5-10秒，请稍候）...",
                fg="#ff8c00")
        elif active_count == 0:
            self.lbl_detect.config(
                text="⏳ 等待玩家活动以识别活跃槽位（饱食度变化即触发）",
                fg="#888")
        else:
            sorted_active = sorted(self.tracker.active_slots)
            slots_str = ", ".join(f"P{s+1}" for s in sorted_active)
            extra = f"  |  反查到 {discovered} 个独立块" if discovered else ""
            if self._discover_failed and active_count > 2:
                extra += "  |  ⚠️ 反查失败"
            self.lbl_detect.config(
                text=f"✅ 活跃槽位: {slots_str}{extra}",
                fg="#006400")

        for i, (row, d) in enumerate(zip(self.row_labels, snapshot)):
            if d.get('is_active'):
                row['fl'].config(bg="#ffffff")
                row['fc'].config(bg="#f5faf5")
                for k in ('tag_live','ln','lr','lf'):
                    row[k].config(bg="#ffffff", fg="#222")
                row['li'].config(bg="#ffffff", fg="red")
                for k in ('tag_cum','cn','cr','cf'):
                    row[k].config(bg="#f5faf5", fg="#3a7d3a")
            else:
                row['fl'].config(bg="#f4f4f4")
                row['fc'].config(bg="#f4f4f4")
                for k in ('tag_live','ln','lr','lf','li',
                          'tag_cum','cn','cr','cf'):
                    row[k].config(bg="#f4f4f4", fg="#bbb")

            if d['valid']:
                row['ln'].config(text=fmt(d['live_n']))
                row['lr'].config(text=fmt(d['live_r']))
                row['lf'].config(text=fmt(d['live_f']))
                row['li'].config(text=fmt(d['live_i']))
                row['cn'].config(text=f"+{d['cum_n']:,}")
                row['cr'].config(text=f"+{d['cum_r']:,}")
                row['cf'].config(
                    text=f"+{d['cum_f']:,}" if d['live_f'] is not None else "—")
            else:
                for k in ('ln','lr','lf','li'):
                    row[k].config(text="---")

        self.root.after(UI_REFRESH_MS, self._ui_tick)

    def _scanner(self):
        OFFSET_RES_PLAYER = 0x1280   # 仅作 1-2 人时的第一跳，多人靠连续行走
        OFFSET_RES_RARE   = 0x80
        OFFSET_ARRAY      = 0x4

        while True:
            time.sleep(SCAN_INTERVAL)
            if not self.pm:
                continue

            self._cache_countdown -= 1
            if self._cache_countdown <= 0:
                self._addr_cache = None
                self._cache_countdown = ADDR_CACHE_TTL

            if self._addr_cache is None:
                p1_n   = self._resolve(*POINTER_CHAINS["普通资源"])
                p1_inf = self._resolve(*POINTER_CHAINS["感染度"])

                p1_f = None
                if p1_inf:
                    # ==========================================
                    # 🛰️ 智能锚点定位：以感染度为基石锁定饱食度
                    # ==========================================
                    if self._food_offset_from_inf is None:
                        # 方案 A：测试首选固定距离 0x0E50 (应对最新版地图)
                        try:
                            test_f = self.pm.read_int(p1_inf + 0x0E50)
                            if 0 <= test_f <= 200:
                                self._food_offset_from_inf = 0x0E50
                                print("[星链] 祖传偏移 0x0E50 命中！")
                        except Exception:
                            pass

                        # 方案 B：如果首选失败，触发开局全员 65 盲搜协议
                        if self._food_offset_from_inf is None:
                            try:
                                print("[星链] 启动 65 盲搜特征定位...")
                                # 将搜索半径扩大 4 倍，扫描前后 32KB (0x8000) 范围
                                search_radius = 0x8000
                                win = self.pm.read_bytes(p1_inf - search_radius, search_radius * 2)
                                target_sig = struct.pack('<5I', 65, 65, 65, 65, 65)
                                idx = win.find(target_sig)
                                if idx != -1:
                                    self._food_offset_from_inf = idx - search_radius
                                    print(f"[星链] 盲搜成功！新距离锁定为: "
                                          f"{hex(self._food_offset_from_inf)}")
                            except Exception:
                                pass

                    # 只要锁定了距离，秒算出饱食度地址
                    if self._food_offset_from_inf is not None:
                        p1_f = p1_inf + self._food_offset_from_inf
                    # ==========================================

                if any((p1_n, p1_inf, p1_f)):
                    self._addr_cache = (p1_n, p1_inf, p1_f)
                else:
                    with self._scan_lock:
                        for i in range(NUM_PLAYERS):
                            self._scan_data[i]['valid'] = False
                    continue
            else:
                p1_n, p1_inf, p1_f = self._addr_cache

            # 阶段1：饱食度/感染度（按槽位索引）
            food_arr = [None] * NUM_PLAYERS
            inf_arr  = [None] * NUM_PLAYERS
            for i in range(NUM_PLAYERS):
                if p1_f:
                    try:
                        f = self.pm.read_int(p1_f + i * OFFSET_ARRAY)
                        if 0 <= f <= 500:
                            food_arr[i] = f
                            self.tracker.mark_food(i, f)
                    except Exception:
                        pass
                if p1_inf:
                    try:
                        inf_arr[i] = self.pm.read_int(
                            p1_inf + i * OFFSET_ARRAY)
                    except Exception:
                        self._addr_cache = None

            # 阶段2：资源（优先反查地址，回退到第一跳 stride）
            for i in range(NUM_PLAYERS):
                normal = rare = None
                used_discovered = False

                # ⭐ 优先使用反查得到的精确地址
                if i in self.player_blocks:
                    try:
                        n_addr = self.player_blocks[i]
                        r_addr = n_addr + OFFSET_RES_RARE
                        n_raw = self.pm.read_int(n_addr)
                        r_raw = self.pm.read_int(r_addr)
                        if (0 <= n_raw <= 99_999_990 and n_raw % 10 == 0
                            and 0 <= r_raw <= 99_999_990 and r_raw % 10 == 0):
                            normal = n_raw // 10
                            rare   = r_raw // 10
                            used_discovered = True
                        else:
                            self.player_blocks.pop(i, None)
                    except Exception:
                        self.player_blocks.pop(i, None)

                # 回退：仅第一跳 stride（dense[0]/dense[1] 可靠）
                if not used_discovered and p1_n:
                    res_idx = self.tracker.slot_to_res_idx(i)
                    if res_idx is not None and res_idx <= 1:
                        try:
                            n_addr = p1_n + res_idx * OFFSET_RES_PLAYER
                            r_addr = n_addr + OFFSET_RES_RARE
                            n_raw = self.pm.read_int(n_addr)
                            r_raw = self.pm.read_int(r_addr)
                            if (0 <= n_raw <= 99_999_990 and n_raw % 10 == 0
                                and 0 <= r_raw <= 99_999_990 and r_raw % 10 == 0):
                                normal = n_raw // 10
                                rare   = r_raw // 10
                            else:
                                normal = rare = None
                        except Exception:
                            normal = rare = None
                            self._addr_cache = None

                # ⭐ 卡死检测：活跃槽位读到的值死活不变 → 算失败
                if (i in self.tracker.active_slots
                    and i not in self.player_blocks
                    and normal is not None):
                    if (self._prev_resource[i] is not None
                        and normal == self._prev_resource[i]):
                        self._resource_stable_count[i] += 1
                    else:
                        self._resource_stable_count[i] = 0
                    self._prev_resource[i] = normal
                else:
                    self._resource_stable_count[i] = 0

                # 累计失败次数（None 或卡死都算）
                if (i in self.tracker.active_slots
                    and i not in self.player_blocks
                    and (normal is None
                         or self._resource_stable_count[i] >= 200)):
                    self._slot_fail_count[i] += 1
                else:
                    self._slot_fail_count[i] = 0

                self.tracker.update(i,
                                    normal=normal, rare=rare, food=food_arr[i])
                cn, cr, cf = self.tracker.get(i)

                with self._scan_lock:
                    self._scan_data[i] = dict(
                        valid=True,
                        live_n=normal, live_r=rare,
                        live_f=food_arr[i], live_i=inf_arr[i],
                        cum_n=cn, cum_r=cr, cum_f=cf,
                        is_active=(i in self.tracker.active_slots),
                    )

            # ⭐ 触发反查：活跃集合变大 或 失败累计
            if not self._discover_running:
                cur_active = frozenset(self.tracker.active_slots)
                missing = [s for s in cur_active
                           if s not in self.player_blocks]

                # 活跃集合发生变化 → 解除失败锁，允许重新反查
                if cur_active != self._last_discover_active:
                    self._discover_failed = False
                    self._discover_attempts = 0

                fail_triggered = any(
                    self._slot_fail_count[i] >= DISCOVER_FAIL_THRESHOLD
                    for i in missing
                )
                need = (
                    len(missing) > 0
                    and not self._discover_failed
                    and (fail_triggered
                         or cur_active != self._last_discover_active)
                )
                if need:
                    self._last_discover_active = cur_active
                    self._discover_running = True
                    threading.Thread(target=self._do_auto_discover,
                                     daemon=True).start()

    # ── 自动反查（后台线程）─────────────────────────────────
    def _do_auto_discover(self):
        try:
            self._discover_attempts += 1
            print(f"[反查] 第 {self._discover_attempts} 次尝试...")
            result = self.discover_player_blocks()

            if result and len(result) > 1:
                merged = dict(self.player_blocks)
                merged.update(result)
                self.player_blocks = merged
                self._slot_fail_count = [0] * NUM_PLAYERS
                self._discover_failed = False
                print(f"[反查] 成功，已记录 {len(self.player_blocks)} 个玩家块")
            else:
                if self._discover_attempts >= 3:
                    self._discover_failed = True
                    print("[反查] 已尝试 3 次失败，停止自动反查")
                else:
                    self._slot_fail_count = [0] * NUM_PLAYERS
        except Exception as e:
            print(f"[反查] 异常: {e}")
        finally:
            self._discover_running = False

    def discover_player_blocks(self):
        """
        ⭐ 连续行走 + DNA 签名（步长无关）。
        关键发现：玩家块连续但大小可变(0x1280/0x1290)，固定步长必累积误差。
        从 dense[0] 出发，用结构签名逐块"走"到下一块，自适应任意步长。
        """
        if not self.pm or not self._addr_cache:
            return None
        p1_n, p1_inf, p1_f = self._addr_cache
        if not p1_n:
            return None

        active = sorted(self.tracker.active_slots)
        n_active = len(active)
        if n_active == 0:
            return None

        BLOCK0 = 0x1280            # 第一段步长（已确认可靠）
        dense0 = p1_n
        dense1 = p1_n + BLOCK0

        if n_active == 1:
            return {active[0]: dense0}
        if n_active == 2:
            return {active[0]: dense0, active[1]: dense1}

        # ── 提取 DNA：两个已知块都相同的非零 4 字节 ──────────
        try:
            blk0 = self.pm.read_bytes(dense0, BLOCK0)
            blk1 = self.pm.read_bytes(dense1, BLOCK0)
        except Exception as e:
            print(f"[行走] 读已知块失败: {e}")
            return None

        dna = []
        for off in range(0, BLOCK0 - 4, 4):
            v0 = struct.unpack_from('<I', blk0, off)[0]
            v1 = struct.unpack_from('<I', blk1, off)[0]
            if v0 == v1 and v0 != 0:
                dna.append((off, v0))

        if len(dna) < 3:
            print(f"[行走] DNA 常量不足 ({len(dna)})，块结构差异过大")
            return None

        # 优先指针样常量（唯一性强）；锚点取第一个
        ptr_like = [(o, v) for o, v in dna if 0x10000 < v < 0x7FFFFFFF]
        use_dna = ptr_like[:6] if len(ptr_like) >= 3 else dna[:10]
        anchor_off, anchor_val = use_dna[0]
        anchor_bytes = struct.pack('<I', anchor_val)
        print(f"[行走] DNA {len(dna)} 常量，验证用 {len(use_dna)} 个，"
              f"锚点 @+{anchor_off:#x} = {anchor_val:#x}")

        def verify(addr):
            try:
                buf = self.pm.read_bytes(addr, BLOCK0)
            except Exception:
                return False
            for fo, fv in use_dna:
                if struct.unpack_from('<I', buf, fo)[0] != fv:
                    return False
            return True

        # ── 连续行走 ────────────────────────────────────────
        SEARCH_LO, SEARCH_HI = 0x1240, 0x1340
        blocks = [dense0, dense1]
        cur = dense1

        for _ in range(n_active - 2):
            read_from = cur + SEARCH_LO
            read_len  = (SEARCH_HI - SEARCH_LO) + BLOCK0 + 0x10
            try:
                window = self.pm.read_bytes(read_from, read_len)
            except Exception:
                print(f"[行走] 窗口读取失败 @ {read_from:#x}")
                break

            nxt = None
            idx = 0
            while True:
                idx = window.find(anchor_bytes, idx)
                if idx == -1:
                    break
                blk_start = read_from + idx - anchor_off
                if (cur + SEARCH_LO <= blk_start <= cur + SEARCH_HI
                        and verify(blk_start)):
                    nxt = blk_start
                    break
                idx += 4

            if nxt is None:
                print(f"[行走] {cur:#x} 之后未找到下一块，停止 "
                      f"(已找到 {len(blocks)} 块)")
                break

            print(f"[行走] 下一块 @ {nxt:#x}  (实测步长 {nxt - cur:#x})")
            blocks.append(nxt)
            cur = nxt

        if len(blocks) < n_active:
            print(f"[行走] 仅找到 {len(blocks)} 块 < 活跃 {n_active}")

        # ── 映射 + 校验 ─────────────────────────────────────
        result = {}
        for i, slot in enumerate(active):
            if i < len(blocks):
                addr = blocks[i]
                result[slot] = addr
                try:
                    nv = self.pm.read_int(addr) // 10
                    rv = self.pm.read_int(addr + 0x80) // 10
                    print(f"[行走] Slot {slot} (P{slot+1}): "
                          f"{addr:#x}  普通={nv} 稀有={rv}")
                except Exception:
                    print(f"[行走] Slot {slot}: {addr:#x} (校验读取失败)")

        return result if len(result) >= 2 else (result or None)

    def _resolve(self, base_off, offsets):
        try:
            addr = self.pm.read_uint(self.game_base + base_off)
            for off in offsets[:-1]:
                addr = self.pm.read_uint(addr + off)
            return addr + offsets[-1]
        except:
            return None

    def _reset_tracker(self):
        self.tracker.reset()
        self.player_blocks      = {}
        self._slot_fail_count   = [0] * NUM_PLAYERS
        self._discover_attempts = 0
        self._discover_failed   = False
        self._food_offset_from_inf = None
        self._resource_stable_count = [0] * NUM_PLAYERS
        self._prev_resource = [None] * NUM_PLAYERS
        self._initial_discovered = False
        self._last_discover_active = None
        for row in self.row_labels:
            row['cn'].config(text="+0")
            row['cr'].config(text="+0")
            row['cf'].config(text="+0")

    def manual_refresh(self):
        self.lbl_status.config(text="检索中...", fg="orange")
        self.root.update()
        for pid, _, _ in find_war3_pids():
            try:
                pm  = pymem.Pymem(pid)
                mod = pymem.process.module_from_name(pm.process_handle, "Game.dll")
                if mod:
                    self.pm        = pm
                    self.game_base = mod.lpBaseOfDll
                    self._addr_cache = None
                    self.tracker.reset()
                    self.player_blocks      = {}
                    self._slot_fail_count   = [0] * NUM_PLAYERS
                    self._discover_attempts = 0
                    self._discover_failed   = False
                    self._food_offset_from_inf = None
                    self._resource_stable_count = [0] * NUM_PLAYERS
                    self._prev_resource = [None] * NUM_PLAYERS
                    self._initial_discovered = False
                    self._last_discover_active = None
                    self.lbl_status.config(
                        text=f"已连接 0x{self.game_base:X}", fg="green")
                    return
            except: continue
        self.lbl_status.config(text="少女祈祷中", fg="red")

    def _watchdog(self):
        while True:
            if self.pm:
                try:    self.pm.read_bytes(self.game_base, 2)
                except:
                    self.pm = None
                    self.game_base = None
                    self._addr_cache = None
                    self.player_blocks      = {}
                    self._slot_fail_count   = [0] * NUM_PLAYERS
                    self._discover_attempts = 0
                    self._discover_failed   = False
                    self._food_offset_from_inf = None
                    self._resource_stable_count = [0] * NUM_PLAYERS
                    self._prev_resource = [None] * NUM_PLAYERS
                    self._initial_discovered = False
                    self._last_discover_active = None
                    self.root.after(0, lambda: self.lbl_status.config(
                        text="游戏已退出", fg="red"))
            else:
                self.root.after(0, self.manual_refresh)
            time.sleep(3)

    def _register_hotkeys(self):
        keyboard.add_hotkey(self.refresh_hotkey,
                            lambda: self.root.after(0, self.manual_refresh))

    def change_key(self):
        threading.Thread(target=self._wait_key, daemon=True).start()

    def _wait_key(self):
        ev = keyboard.read_event(suppress=True)
        while ev.event_type != keyboard.KEY_DOWN:
            ev = keyboard.read_event(suppress=True)
        new_key = ev.name
        try: keyboard.remove_hotkey(self.refresh_hotkey)
        except: pass
        self.refresh_hotkey = new_key
        keyboard.add_hotkey(new_key,
                            lambda: self.root.after(0, self.manual_refresh))
        self.root.after(0, lambda: self.btn_refresh.config(
            text=f"↻ 刷新 ({self.refresh_hotkey.upper()})"))


if __name__ == "__main__":
    root = tk.Tk()
    War3StatsApp(root)
    root.mainloop()