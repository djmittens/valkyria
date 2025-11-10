# Game Engine Scripting Path

## Vision: Live-Coded Games in Valkyria

The game engine path positions Valkyria as **the language for interactive game development**. The killer feature: modify game logic, AI, physics, and rendering **while the game is running** without losing state.

## Why Games First?

**Games validate the hard requirements:**
- Embeddability (scripting in C/C++ engines)
- Performance (60+ FPS real-time constraints)
- Hot reload (modify code without restart)
- FFI (calling graphics/physics libraries)
- Memory management (allocations per frame)
- REPL integration (live coding)

**If Valkyria works for games, everything else becomes easy.**

## Target Experience

```lisp
; game.valk - Running game, 60 FPS

(def {enemy-speed} 5.0)
(def {player-health} 100)

(defun on-update [dt]
  (when (key-down? :w)
    (move-player! :up (* player-speed dt)))

  (for-each enemy enemies
    (update-enemy! enemy dt enemy-speed))

  (check-collisions!))

(defun on-render []
  (draw-sprite player (:x player) (:y player))
  (for-each enemy enemies
    (draw-sprite enemy (:x enemy) (:y enemy)))
  (draw-text (str "HP: " player-health) 10 10 WHITE))
```

**In REPL (while game running):**
```lisp
> (def {enemy-speed} 10.0)  ; Enemies now move faster - instantly!
> (def {player-health} 200) ; Double health - no restart needed!
> ; Redefine entire AI function
> (defun update-enemy! [enemy dt speed]
>   ; New pathfinding logic here
> )
```

## Phases

### Phase 1: Networking Foundation (Current)
**Status**: In progress
**Timeline**: 3 weeks
**See**: `NETWORKING_BRANCH_TASKS.md`

**Deliverables:**
- HTTP server/client in Lisp
- Async I/O with futures
- Test framework
- REPL safety basics

**Why needed for games**: Multiplayer games need networking, test framework needed for validating game logic.

---

### Phase 2: Embedding & FFI (CRITICAL FOR GAMES)
**Timeline**: 3-4 weeks after Phase 1
**Estimated effort**: 15-20 days

#### Task 2.1: C Embedding API (5-6 days)

**Goal**: Allow C/C++ programs to embed Valkyria runtime.

**API to implement:**
```c
// Initialize runtime
valk_runtime_t* valk_runtime_new(void);
void valk_runtime_free(valk_runtime_t* rt);

// Load and execute scripts
int valk_runtime_load_file(valk_runtime_t* rt, const char* filepath);
int valk_runtime_eval(valk_runtime_t* rt, const char* code);

// Call Lisp functions from C
valk_lval_t* valk_runtime_call(valk_runtime_t* rt, const char* fn_name,
                                int argc, valk_lval_t** args);

// Register C functions callable from Lisp
void valk_runtime_register_cfunc(valk_runtime_t* rt, const char* name,
                                  valk_builtin_func func);

// Access global environment
valk_lval_t* valk_runtime_get_global(valk_runtime_t* rt, const char* name);
void valk_runtime_set_global(valk_runtime_t* rt, const char* name, valk_lval_t* val);
```

**Example usage in C game:**
```c
// In your game engine
valk_runtime_t* script_rt = valk_runtime_new();
valk_runtime_load_file(script_rt, "game.valk");

// Game loop
while (running) {
    double dt = get_delta_time();
    valk_lval_t* dt_val = valk_lval_num(dt);
    valk_runtime_call(script_rt, "on_update", 1, &dt_val);

    render_frame();
    valk_runtime_call(script_rt, "on_render", 0, NULL);
}

valk_runtime_free(script_rt);
```

**Implementation locations:**
- `src/embed.c` - New file for embedding API
- `src/embed.h` - Public header for game engines
- Update `src/repl.c` to use the new runtime API

**Testing:**
- Create `test/test_embed.c` with example embedded usage
- Test calling Lisp from C, C from Lisp
- Test multiple runtimes in same process

---

#### Task 2.2: FFI - Foreign Function Interface (4-5 days)

**Goal**: Call C functions from Lisp dynamically.

**Lisp API:**
```lisp
; Load shared library
(ffi/load "libraylib.so")

; Bind C function: (ffi/bind lib-name fn-name arg-types return-type)
(ffi/bind "libraylib" "InitWindow" [:int :int :string] :void)
(ffi/bind "libraylib" "WindowShouldClose" [] :int)
(ffi/bind "libraylib" "BeginDrawing" [] :void)
(ffi/bind "libraylib" "EndDrawing" [] :void)
(ffi/bind "libraylib" "DrawRectangle" [:int :int :int :int :color] :void)

; Call bound functions
(InitWindow 800 600 "Valkyria Game")
(while (== (WindowShouldClose) 0)
  (BeginDrawing)
  (DrawRectangle 100 100 200 150 RED)
  (EndDrawing))
```

**C type mapping:**
```
Lisp Type    C Type          Notes
:int         int32_t
:float       float
:double      double
:string      const char*     Null-terminated
:ptr         void*           Opaque pointer
:void        void            Return only
:color       uint32_t        RGBA packed (or custom struct)
```

**Implementation:**
- Use `libffi` or `dyncall` library for dynamic C calls
- Add `src/ffi.c` and `src/ffi.h`
- Builtin functions:
  - `valk_builtin_ffi_load()`
  - `valk_builtin_ffi_bind()`
  - Generated wrapper functions per binding

**Type safety:**
- Validate arg count and types at call time
- Marshal Lisp values to C types (with error checking)
- Unmarshal C return values to Lisp values

**Testing:**
- Bind to simple C standard library functions (strlen, sin, cos)
- Test with a real library (SDL2 or raylib)
- Test error handling (wrong arg types, wrong arg count)

---

#### Task 2.3: Basic Graphics Bindings (2-3 days)

**Goal**: Provide ready-to-use graphics library.

**Choose one**: raylib (easiest), SDL2 (more flexible), or custom minimal renderer

**Example with raylib:**
```lisp
; prelude_graphics.valk - Included with Valkyria

; Colors (constants)
(def {WHITE} 0xFFFFFFFF)
(def {BLACK} 0x000000FF)
(def {RED}   0xFF0000FF)
(def {GREEN} 0x00FF00FF)
(def {BLUE}  0x0000FFFF)

; Raylib bindings (auto-generated or manual)
(ffi/load "libraylib.so")
(ffi/bind "libraylib" "InitWindow" [:int :int :string] :void)
(ffi/bind "libraylib" "SetTargetFPS" [:int] :void)
(ffi/bind "libraylib" "WindowShouldClose" [] :int)
(ffi/bind "libraylib" "BeginDrawing" [] :void)
(ffi/bind "libraylib" "EndDrawing" [] :void)
(ffi/bind "libraylib" "ClearBackground" [:color] :void)
(ffi/bind "libraylib" "DrawRectangle" [:int :int :int :int :color] :void)
(ffi/bind "libraylib" "DrawCircle" [:int :int :float :color] :void)
(ffi/bind "libraylib" "DrawText" [:string :int :int :int :color] :void)
(ffi/bind "libraylib" "IsKeyDown" [:int] :int)

; Key constants (raylib key codes)
(def {KEY_W} 87)
(def {KEY_A} 65)
(def {KEY_S} 83)
(def {KEY_D} 68)
(def {KEY_SPACE} 32)

; Helper functions
(fun {key-down? key} {
  (!= (IsKeyDown key) 0)
})
```

**Implementation:**
- Create `src/prelude_graphics.valk`
- Document raylib installation requirement
- Provide installation script for common platforms

**Alternative**: Minimal custom renderer using OpenGL if you want zero dependencies.

---

#### Task 2.4: Demo Game - Pong (3-4 days)

**Goal**: Build a complete playable game demonstrating hot reload.

**Game features:**
- Two paddles (player vs AI)
- Ball physics with collision
- Score tracking
- Win condition

**File structure:**
```
examples/pong/
  main.c          - C harness (initializes window, calls Lisp)
  game.valk       - Main game logic (hot-reloadable)
  paddle.valk     - Paddle entity
  ball.valk       - Ball entity
  ai.valk         - AI opponent (hot-reloadable for tuning)
  Makefile        - Build game
```

**game.valk:**
```lisp
(load "src/prelude.valk")
(load "src/prelude_graphics.valk")
(load "examples/pong/paddle.valk")
(load "examples/pong/ball.valk")
(load "examples/pong/ai.valk")

; Game state (preserved across hot reloads!)
(def {player1} (paddle-new 20 250))
(def {player2} (paddle-new 760 250))
(def {ball} (ball-new 400 300))
(def {score1} 0)
(def {score2} 0)

(defun on-update [dt]
  ; Player 1 controls
  (when (key-down? KEY_W) (paddle-move! player1 :up dt))
  (when (key-down? KEY_S) (paddle-move! player1 :down dt))

  ; AI player 2
  (ai-update! player2 ball dt)

  ; Ball physics
  (ball-update! ball dt)
  (ball-check-paddle-collision! ball player1)
  (ball-check-paddle-collision! ball player2)

  ; Scoring
  (when (< (:x ball) 0)
    (do
      (= {score2} (+ score2 1))
      (ball-reset! ball)))
  (when (> (:x ball) 800)
    (do
      (= {score1} (+ score1 1))
      (ball-reset! ball))))

(defun on-render []
  (ClearBackground BLACK)
  (paddle-draw player1)
  (paddle-draw player2)
  (ball-draw ball)
  (DrawText (str score1) 350 20 40 WHITE)
  (DrawText (str score2) 430 20 40 WHITE)

  ; Win condition
  (when (>= score1 5)
    (DrawText "Player 1 Wins!" 250 300 40 GREEN))
  (when (>= score2 5)
    (DrawText "Player 2 Wins!" 250 300 40 RED)))
```

**Hot reload demo:**
1. Start game
2. While playing, open REPL
3. `(def {ai-difficulty} 0.5)` - Make AI slower
4. `(def {ball-speed} 8.0)` - Speed up ball
5. Redefine `ai-update!` with new behavior
6. **Game instantly reflects changes without restart**

**Implementation:**
- C `main.c` sets up window, loads script, calls on-update/on-render
- File watcher (optional) auto-reloads on save
- Preserve game state across reloads (crucial!)

---

#### Task 2.5: Hot Reload System (3-4 days)

**Goal**: Reload Lisp code without restarting the program or losing state.

**Challenges:**
- Preserve game state (player position, score, etc.)
- Update function definitions
- Handle errors gracefully (rollback on failure)
- Detect file changes

**Strategy:**
```lisp
; State is stored in global environment
; When reloading:
; 1. Save current state (all `def` bindings)
; 2. Re-evaluate file
; 3. Restore state (only functions are updated, data preserved)
```

**API:**
```c
// In C embedding API
int valk_runtime_reload(valk_runtime_t* rt);
```

```lisp
; In Lisp
(reload "game.valk")  ; Re-eval file, preserve globals
```

**File watching (optional):**
- Use inotify (Linux) / FSEvents (macOS) / ReadDirectoryChangesW (Windows)
- Auto-reload on file save
- Show notification in game when reload happens

**Error handling:**
- If reload fails (syntax error), keep old code
- Show error in REPL/console
- Don't crash game

**Testing:**
- Modify function while game running
- Modify data while game running
- Introduce syntax error during reload
- Verify state preservation

---

### Phase 3: Type System (for Safety)
**Timeline**: 1-2 months after Phase 2
**See**: `VISION.md` Phase 2

**Why needed for games:**
- Catch bugs at compile-time (typos, wrong arg types)
- Better IDE support (autocomplete for game entities)
- Performance (type inference enables optimizations)

**Example typed game code:**
```lisp
(: Vec2 (Record :x Float :y Float))
(: Paddle (Record :pos Vec2 :vel Vec2 :width Int :height Int))

(defun paddle-update! [paddle: Paddle, dt: Float] -> Void
  (= (:y (:pos paddle)) (+ (:y (:pos paddle)) (* (:y (:vel paddle)) dt))))
```

**Type system validates:**
- Entity structure (all paddles have x, y, width, height)
- Function signatures (can't pass Int where Float expected)
- Missing fields

---

### Phase 4: Advanced Game Features
**Timeline**: After type system
**Pick and choose based on needs**

#### Option A: Entity Component System (ECS)
```lisp
(def {world} (ecs/world-new))

; Define components
(defcomponent Position :x :y)
(defcomponent Velocity :dx :dy)
(defcomponent Sprite :texture :width :height)

; Create entities
(def {player} (ecs/entity world))
(ecs/add player (Position 100 100))
(ecs/add player (Velocity 0 0))
(ecs/add player (Sprite "player.png" 32 32))

; Systems process components
(defsystem MovementSystem [Position Velocity]
  (fn [pos vel dt]
    (= (:x pos) (+ (:x pos) (* (:dx vel) dt)))
    (= (:y pos) (+ (:y pos) (* (:dy vel) dt)))))

(ecs/run-system world MovementSystem dt)
```

#### Option B: Physics Integration
```lisp
; Bind to box2d or similar
(ffi/load "libbox2d.so")
(def {world} (b2World-new 0 -10))  ; Gravity
(def {body} (b2Body-new world :dynamic 100 100))
(b2Body-apply-force body 0 1000)
```

#### Option C: Audio
```lisp
(ffi/load "libopenal.so")
(def {music} (audio/load "background.ogg"))
(audio/play music :loop true)
(def {sfx} (audio/load "explosion.wav"))
(audio/play sfx)
```

#### Option D: Networking (Multiplayer)
```lisp
; Already have HTTP/2! Build on it:
(def {server} (game/server 8080))
(game/broadcast server {:event :player-moved :x 100 :y 200})

; Client
(def {client} (game/connect "127.0.0.1" 8080))
(game/on-message client
  (fn [msg]
    (update-remote-player! msg)))
```

---

## Milestones & Demos

### Milestone 1: "Hello Triangle" (End of Phase 2.1)
```lisp
(InitWindow 800 600 "Valkyria Graphics")
(while (!= (WindowShouldClose) 1)
  (BeginDrawing)
  (DrawTriangle 400 100 300 400 500 400 RED)
  (EndDrawing))
```
**Proves**: Embedding + FFI work

### Milestone 2: "Interactive Demo" (End of Phase 2.2)
```lisp
(def {x} 400)
(def {y} 300)
(defun on-update [dt]
  (when (key-down? KEY_D) (= {x} (+ x 5)))
  (when (key-down? KEY_A) (= {x} (- x 5)))
  (when (key-down? KEY_W) (= {y} (- y 5)))
  (when (key-down? KEY_S) (= {y} (+ y 5))))
(defun on-render []
  (ClearBackground BLACK)
  (DrawCircle x y 20 GREEN))
```
**Proves**: Game loop integration works

### Milestone 3: "Pong" (End of Phase 2.4)
Complete playable game with AI, physics, scoring.
**Proves**: Real game development is viable

### Milestone 4: "Live-Coded Pong" (End of Phase 2.5)
Pong running, REPL connected, modify AI/physics while playing.
**Proves**: The vision works - you can live-code games!

### Milestone 5: "Typed Game" (End of Phase 3)
Pong rewritten with type annotations, compile-time validation.
**Proves**: Type system adds safety without sacrificing flexibility

---

## Success Metrics

**Technical:**
- Game runs at 60 FPS minimum
- Hot reload takes <100ms
- REPL response time <50ms
- Zero crashes during live coding session

**Experience:**
- Can modify game logic without restart
- Can tweak parameters (speed, colors, etc.) live
- Errors don't crash game, just show in REPL
- Game state preserved across reloads

**Demo:**
- 5-minute video showing Pong being developed live
- Tweak AI difficulty in real-time
- Change ball physics while playing
- Modify rendering on the fly
- **"This is the future of game development"**

---

## Resources Required

**Dependencies:**
- raylib (or SDL2) - Graphics library
- libffi (or dyncall) - FFI implementation
- inotify/FSEvents - File watching (optional)

**New code:**
- `src/embed.c/h` - Embedding API (~500 lines)
- `src/ffi.c/h` - FFI system (~800 lines)
- `src/prelude_graphics.valk` - Graphics bindings (~200 lines)
- `examples/pong/*.valk` - Demo game (~400 lines)
- `test/test_embed.c` - Embedding tests (~200 lines)

**Total new code:** ~2000-2500 lines

**Timeline:** 3-4 weeks of focused work

---

## Next Steps After Game Engine

Once game engine works, you've validated:
- ✅ Embeddability
- ✅ Performance
- ✅ Hot reload
- ✅ FFI
- ✅ Real-time constraints

**Then you can tackle:**
1. More complex games (platformer, RPG, etc.)
2. Full game engine (not just scripting)
3. Mobile deployment (iOS/Android)
4. WebAssembly (games in browser)
5. Visual editor (drag-drop game creation)

**Or pivot to:**
- CI systems (now easy with FFI)
- Web servers (already have HTTP/2)
- Desktop apps (same embedding tech)

---

**Last Updated**: 2025-11-09
**Status**: Planning
**Dependencies**: Networking branch completion
