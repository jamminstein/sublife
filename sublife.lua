-- sublife
-- a living bass sequencer
--
-- ▼ bass lines that breathe ▼
--
-- inspired by LCD Soundsystem,
-- Flea, Daft Punk
--
-- ENC1: pocket lock (variation)
-- ENC2: scroll parameters
-- ENC3: adjust value
-- KEY2: play / stop
-- KEY3: tap=mutate, hold=reset
--
-- Grid (16x8):
--   rows 1-6: piano roll
--   row 7: accent pattern
--   row 8: controls
--
-- v1.0

engine.name = "Sublife"

local musicutil = require "musicutil"
local lattice_lib = require "lattice"

----------------------------------------------------------------
-- CONSTANTS
----------------------------------------------------------------
local NUM_STEPS = 16
local NUM_BANKS = 4
local GRID_PITCH_ROWS = 6
local GRID_ACCENT_ROW = 7
local GRID_CTRL_ROW = 8

local ARTIC = {
  REST  = 0,
  PLUCK = 1,
  SLAP  = 2,
  MUTE  = 3,
  SLIDE = 4,
  GHOST = 5
}

local ARTIC_NAMES = {
  [0] = "rest", "pluck", "slap", "mute", "slide", "ghost"
}

local BRIGHT = {
  OFF    = 0,
  GHOST  = 2,
  DIM    = 4,
  MID    = 8,
  BRIGHT = 12,
  FULL   = 15
}

local SCALE_NAMES = {
  "Minor Pentatonic", "Dorian", "Mixolydian",
  "Phrygian", "Natural Minor", "Blues",
  "Whole Tone", "Chromatic"
}

local ARC_SHAPES = { "sine", "triangle", "ramp_up", "ramp_down", "drift" }

----------------------------------------------------------------
-- STATE
----------------------------------------------------------------
local g = grid.connect()
local my_lattice
local seq_sprocket
local metro_redraw

local playing = false
local current_step = 0
local current_bank = 1
local pattern_length = 16
local root_note = 36 -- C2
local scale_type = 1
local scale_notes = {}

-- pattern storage
local home_patterns = {}   -- the "truth" / home groove
local live_patterns = {}   -- what actually plays (after mutations)

-- variation system
local pocket_lock = 65     -- 0=wild, 100=locked to home
local mutation_rate = 25   -- base probability of mutation per step per phrase cycle

-- arc system (long-form macro sweeps)
local arc_phase = 0
local arc_speed = 4        -- how many bars per full arc cycle
local arc_shape = 1        -- index into ARC_SHAPES
local arc_depth = 0.6      -- 0-1, how much the arc affects cutoff
local arc_cutoff_min = 150
local arc_cutoff_max = 5000
local arc_drift_val = 0.5  -- random walk state

-- fill system
local phrase_length = 4        -- bars per phrase
local fill_probability = 35    -- % chance of fill at phrase boundary
local beat_count = 0
local bar_count = 0
local bar_in_phrase = 0
local fill_active = false
local fill_steps_remaining = 0
local fill_data = {}

-- groove / swing
local swing_amount = 0      -- 0=straight, 100=full triplet swing

-- screen
local screen_dirty = true
local selected_param = 1
local page = 1 -- 1=main, 2=sound, 3=arcs

local param_pages = {
  { -- page 1: groove
    { name = "pocket lock", key = "pocket_lock" },
    { name = "mutation", key = "mutation_rate" },
    { name = "swing", key = "swing_amount" },
    { name = "fill prob", key = "fill_probability" },
    { name = "phrase len", key = "phrase_length" },
    { name = "pat length", key = "pattern_length" },
  },
  { -- page 2: sound
    { name = "root", key = "root_note" },
    { name = "scale", key = "scale_type" },
    { name = "cutoff", key = "cutoff" },
    { name = "resonance", key = "resonance" },
    { name = "drive", key = "drive" },
    { name = "sub mix", key = "sub_mix" },
    { name = "saw mix", key = "saw_mix" },
  },
  { -- page 3: arcs
    { name = "arc speed", key = "arc_speed" },
    { name = "arc shape", key = "arc_shape" },
    { name = "arc depth", key = "arc_depth" },
    { name = "filt env", key = "filt_env_amt" },
    { name = "amp decay", key = "amp_dec" },
    { name = "slide time", key = "slide_time" },
  }
}

-- key hold tracking
local key3_time = 0

-- markov chain for note transitions (scale degree transitions)
-- rows = current degree, cols = probability of next degree
-- biased toward root, fifth, and nearby motion
local markov = {
  { 30, 10, 15, 5, 20, 10, 10 }, -- from degree 1
  { 25, 10, 20, 10, 10, 15, 10 }, -- from degree 2
  { 20, 15, 10, 20, 10, 10, 15 }, -- from degree 3
  { 15, 10, 20, 10, 20, 15, 10 }, -- from degree 4
  { 25, 10, 10, 15, 10, 15, 15 }, -- from degree 5
  { 20, 15, 10, 10, 20, 10, 15 }, -- from degree 6
  { 30, 10, 15, 10, 15, 10, 10 }, -- from degree 7
}

----------------------------------------------------------------
-- UTILITIES
----------------------------------------------------------------

local function deep_copy(t)
  if type(t) ~= "table" then return t end
  local copy = {}
  for k, v in pairs(t) do
    copy[k] = deep_copy(v)
  end
  return copy
end

local function weighted_choice(weights)
  local sum = 0
  for _, w in ipairs(weights) do sum = sum + w end
  local r = math.random() * sum
  local acc = 0
  for i, w in ipairs(weights) do
    acc = acc + w
    if r <= acc then return i end
  end
  return #weights
end

local function clamp(val, lo, hi)
  return math.max(lo, math.min(hi, val))
end

local function find_scale_index(note, scale)
  for i, n in ipairs(scale) do
    if n == note then return i end
  end
  -- find nearest
  local best_i, best_d = 1, 999
  for i, n in ipairs(scale) do
    local d = math.abs(n - note)
    if d < best_d then best_i, best_d = i, d end
  end
  return best_i
end

local function snap_to_scale(note)
  if #scale_notes == 0 then return note end
  return musicutil.snap_note_to_array(note, scale_notes)
end

----------------------------------------------------------------
-- SCALE BUILDING
----------------------------------------------------------------

local function build_scale()
  scale_notes = musicutil.generate_scale(root_note - 12, SCALE_NAMES[scale_type], 4)
end

----------------------------------------------------------------
-- PATTERN DATA
----------------------------------------------------------------

local function empty_step()
  return {
    note   = 0,       -- 0 = rest, else MIDI note
    vel    = 100,      -- 0-127
    dur    = 0.5,      -- gate length as fraction of step
    artic  = ARTIC.PLUCK,
    prob   = 100,      -- 0-100
    accent = false,
    micro  = 0,        -- micro timing offset in ms
  }
end

local function init_patterns()
  for bank = 1, NUM_BANKS do
    home_patterns[bank] = {}
    live_patterns[bank] = {}
    for s = 1, NUM_STEPS do
      home_patterns[bank][s] = empty_step()
      live_patterns[bank][s] = empty_step()
    end
  end
  seed_groove(1)
end

-- Seed bank 1 with a funky LCD/Flea-inspired groove
local function seed_groove(bank)
  local r = root_note
  local p5 = root_note + 7
  local m3 = root_note + 3
  local sub = root_note - 12
  local p = home_patterns[bank]

  -- A 16-step groove: 16th note grid
  -- Beat 1: strong root
  p[1]  = { note=r,   vel=120, dur=0.8, artic=ARTIC.PLUCK, prob=100, accent=true,  micro=0 }
  p[2]  = { note=0,   vel=0,   dur=0,   artic=ARTIC.REST,  prob=100, accent=false, micro=0 }
  p[3]  = { note=r,   vel=40,  dur=0.3, artic=ARTIC.GHOST, prob=70,  accent=false, micro=0 }
  p[4]  = { note=0,   vel=0,   dur=0,   artic=ARTIC.REST,  prob=100, accent=false, micro=0 }
  -- Beat 2: fifth with slap
  p[5]  = { note=p5,  vel=110, dur=0.5, artic=ARTIC.SLAP,  prob=100, accent=false, micro=0 }
  p[6]  = { note=r,   vel=35,  dur=0.2, artic=ARTIC.GHOST, prob=55,  accent=false, micro=0 }
  p[7]  = { note=0,   vel=0,   dur=0,   artic=ARTIC.REST,  prob=100, accent=false, micro=0 }
  p[8]  = { note=m3,  vel=60,  dur=0.3, artic=ARTIC.MUTE,  prob=80,  accent=false, micro=0 }
  -- Beat 3: root return, accent
  p[9]  = { note=r,   vel=115, dur=0.7, artic=ARTIC.PLUCK, prob=100, accent=true,  micro=0 }
  p[10] = { note=0,   vel=0,   dur=0,   artic=ARTIC.REST,  prob=100, accent=false, micro=0 }
  p[11] = { note=r,   vel=45,  dur=0.25,artic=ARTIC.GHOST, prob=65,  accent=false, micro=0 }
  p[12] = { note=r+5, vel=70,  dur=0.4, artic=ARTIC.SLIDE, prob=75,  accent=false, micro=0 }
  -- Beat 4: tension, leading back
  p[13] = { note=p5,  vel=105, dur=0.5, artic=ARTIC.PLUCK, prob=95,  accent=false, micro=0 }
  p[14] = { note=r,   vel=30,  dur=0.2, artic=ARTIC.GHOST, prob=50,  accent=false, micro=0 }
  p[15] = { note=sub, vel=95,  dur=0.5, artic=ARTIC.PLUCK, prob=85,  accent=false, micro=0 }
  p[16] = { note=r-1, vel=65,  dur=0.3, artic=ARTIC.SLIDE, prob=70,  accent=false, micro=0 }

  -- copy to live
  for s = 1, NUM_STEPS do
    live_patterns[bank][s] = deep_copy(home_patterns[bank][s])
  end
end

-- forward declaration fix
seed_groove = seed_groove

----------------------------------------------------------------
-- MUTATION ENGINE
-- The heart of sublife: musically intelligent variation
----------------------------------------------------------------

local mutation_types = {
  {
    name = "note_shift",
    weight = 30,
    fn = function(step_data)
      if step_data.note == 0 then return end
      local idx = find_scale_index(step_data.note, scale_notes)
      local dir = math.random() > 0.5 and 1 or -1
      local new_idx = clamp(idx + dir, 1, #scale_notes)
      step_data.note = scale_notes[new_idx]
    end
  },
  {
    name = "octave_jump",
    weight = 8,
    fn = function(step_data)
      -- Daft Punk style: sudden octave displacement
      if step_data.note == 0 then return end
      local dir = math.random() > 0.6 and 12 or -12
      local new_note = step_data.note + dir
      if new_note >= 24 and new_note <= 72 then
        step_data.note = new_note
      end
    end
  },
  {
    name = "ghost_inject",
    weight = 25,
    fn = function(step_data)
      -- Turn a rest into a ghost note, or make a note ghostly
      if step_data.note == 0 then
        -- inject a ghost note where there was silence
        local idx = math.random(1, math.min(7, #scale_notes))
        step_data.note = scale_notes[idx]
        step_data.vel = math.random(20, 45)
        step_data.dur = 0.2 + math.random() * 0.2
        step_data.artic = ARTIC.GHOST
        step_data.prob = math.random(40, 70)
      else
        step_data.vel = math.random(25, 45)
        step_data.artic = ARTIC.GHOST
      end
    end
  },
  {
    name = "accent_shift",
    weight = 15,
    fn = function(step_data)
      if step_data.note == 0 then return end
      step_data.vel = math.random(110, 127)
      step_data.accent = true
    end
  },
  {
    name = "rest_carve",
    weight = 12,
    fn = function(step_data)
      -- Sometimes silence IS the variation
      step_data.note = 0
      step_data.artic = ARTIC.REST
      step_data.vel = 0
    end
  },
  {
    name = "artic_swap",
    weight = 20,
    fn = function(step_data)
      if step_data.note == 0 then return end
      local options = { ARTIC.PLUCK, ARTIC.SLAP, ARTIC.MUTE, ARTIC.SLIDE }
      step_data.artic = options[math.random(#options)]
    end
  },
  {
    name = "chromatic_approach",
    weight = 12,
    fn = function(step_data)
      -- Flea-style: chromatic leading tone
      if step_data.note == 0 then return end
      local dir = math.random() > 0.5 and -1 or 1
      step_data.note = step_data.note + dir
      step_data.dur = 0.25
      step_data.artic = ARTIC.SLIDE
    end
  },
  {
    name = "markov_leap",
    weight = 10,
    fn = function(step_data)
      -- Use the Markov chain to pick a new note based on current
      if step_data.note == 0 then return end
      local idx = find_scale_index(step_data.note, scale_notes)
      -- map to scale degree (mod 7)
      local degree = ((idx - 1) % 7) + 1
      local next_degree = weighted_choice(markov[degree])
      -- find the note at that degree in same octave region
      local octave = math.floor((idx - 1) / 7)
      local new_idx = clamp(octave * 7 + next_degree, 1, #scale_notes)
      step_data.note = scale_notes[new_idx]
    end
  },
  {
    name = "vel_drift",
    weight = 20,
    fn = function(step_data)
      if step_data.note == 0 then return end
      local drift = math.random(-20, 20)
      step_data.vel = clamp(step_data.vel + drift, 20, 127)
    end
  },
  {
    name = "prob_drift",
    weight = 15,
    fn = function(step_data)
      local drift = math.random(-15, 15)
      step_data.prob = clamp(step_data.prob + drift, 20, 100)
    end
  },
}

local function mutate_step(step_idx)
  local home = home_patterns[current_bank][step_idx]
  local live = live_patterns[current_bank][step_idx]

  -- Pocket lock determines mutation probability
  -- At pocket_lock=100, almost no mutations
  -- At pocket_lock=0, mutations happen freely
  local mutation_chance = (100 - pocket_lock) * mutation_rate / 100 / 100

  if math.random() > mutation_chance then
    -- No mutation: drift back toward home (gravity)
    -- Blend 20% back toward home values
    if home.note > 0 and live.note > 0 then
      if math.random() < 0.2 then
        live.note = home.note
        live.vel = home.vel
        live.artic = home.artic
        live.dur = home.dur
        live.prob = home.prob
      end
    end
    return
  end

  -- Pick a mutation type (weighted)
  local weights = {}
  for _, m in ipairs(mutation_types) do
    table.insert(weights, m.weight)
  end
  local choice = weighted_choice(weights)
  mutation_types[choice].fn(live)
end

-- Mutate the entire live pattern (called at phrase boundaries)
local function mutate_pattern()
  for s = 1, pattern_length do
    mutate_step(s)
  end
  screen_dirty = true
end

-- Forcefully mutate (KEY3 tap)
local function force_mutate()
  -- More aggressive mutation: hit every step with higher probability
  local saved_lock = pocket_lock
  pocket_lock = math.max(0, pocket_lock - 40)
  for s = 1, pattern_length do
    -- Double chance
    mutate_step(s)
    mutate_step(s)
  end
  pocket_lock = saved_lock
  screen_dirty = true
end

-- Reset live to home
local function reset_to_home()
  for s = 1, NUM_STEPS do
    live_patterns[current_bank][s] = deep_copy(home_patterns[current_bank][s])
  end
  screen_dirty = true
end

-- Capture live as new home
local function capture_to_home()
  for s = 1, NUM_STEPS do
    home_patterns[current_bank][s] = deep_copy(live_patterns[current_bank][s])
  end
  screen_dirty = true
end

----------------------------------------------------------------
-- ARC SYSTEM (long-form macro parameter sweeps)
----------------------------------------------------------------

local function arc_value()
  local shape = ARC_SHAPES[arc_shape]
  local p = arc_phase

  if shape == "sine" then
    return (math.sin(p * 2 * math.pi) + 1) / 2
  elseif shape == "triangle" then
    return p < 0.5 and (p * 2) or ((1 - p) * 2)
  elseif shape == "ramp_up" then
    return p
  elseif shape == "ramp_down" then
    return 1 - p
  elseif shape == "drift" then
    -- random walk, slowly wandering
    arc_drift_val = clamp(
      arc_drift_val + (math.random() - 0.5) * 0.08,
      0, 1
    )
    return arc_drift_val
  end
  return 0.5
end

local function advance_arc()
  if arc_speed <= 0 then return end
  local increment = 1 / (arc_speed * pattern_length)
  arc_phase = (arc_phase + increment) % 1.0

  -- Apply arc to filter cutoff
  local av = arc_value()
  local cutoff = arc_cutoff_min + (arc_cutoff_max - arc_cutoff_min) * av * arc_depth
  cutoff = cutoff + arc_cutoff_min * (1 - arc_depth) -- base cutoff when depth < 1
  engine.cutoff(cutoff)
end

----------------------------------------------------------------
-- FILL SYSTEM
----------------------------------------------------------------

local function generate_fill()
  fill_data = {}
  local fill_type = math.random(1, 5)
  local fill_len = math.random(2, 6) -- steps

  if fill_type == 1 then
    -- Chromatic run (Flea style)
    local start_note = scale_notes[math.random(1, math.min(5, #scale_notes))]
    for i = 1, fill_len do
      fill_data[i] = {
        note = start_note + (i - 1),
        vel = 90 + math.random(0, 30),
        dur = 0.3,
        artic = ARTIC.SLIDE,
      }
    end
  elseif fill_type == 2 then
    -- Octave bounce (Daft Punk style)
    local base = root_note
    for i = 1, fill_len do
      fill_data[i] = {
        note = i % 2 == 1 and base or base + 12,
        vel = 100 + math.random(0, 27),
        dur = 0.4,
        artic = ARTIC.PLUCK,
      }
    end
  elseif fill_type == 3 then
    -- Slap burst (Flea)
    for i = 1, fill_len do
      local idx = math.random(1, math.min(7, #scale_notes))
      fill_data[i] = {
        note = scale_notes[idx],
        vel = 100 + math.random(0, 27),
        dur = 0.2,
        artic = ARTIC.SLAP,
      }
    end
  elseif fill_type == 4 then
    -- Silence (the most powerful fill)
    for i = 1, fill_len do
      fill_data[i] = {
        note = 0,
        vel = 0,
        dur = 0,
        artic = ARTIC.REST,
      }
    end
  elseif fill_type == 5 then
    -- Root pedal 16ths (LCD Soundsystem motorik build)
    for i = 1, fill_len do
      fill_data[i] = {
        note = root_note,
        vel = 70 + i * 8,
        dur = 0.5,
        artic = ARTIC.MUTE,
      }
    end
  end

  fill_active = true
  fill_steps_remaining = fill_len
end

----------------------------------------------------------------
-- SEQUENCER CORE
----------------------------------------------------------------

local function note_on(step_data)
  if step_data.note == 0 or step_data.artic == ARTIC.REST then return end

  -- probability gate
  if math.random(100) > step_data.prob then return end

  local freq = musicutil.note_num_to_freq(step_data.note)
  local vel = step_data.vel / 127
  local cutoff = params:get("cutoff")
  local artic = step_data.artic
  local slide = params:get("slide_time")

  engine.note_on(freq, vel, cutoff, artic, slide)

  -- schedule note off based on duration
  local step_dur = clock.get_beat_sec() / 4 -- 16th note duration
  clock.run(function()
    clock.sleep(step_dur * step_data.dur)
    engine.note_off()
  end)
end

local function step_advance()
  if not playing then return end

  current_step = (current_step % pattern_length) + 1

  -- Track bars and phrases
  if current_step == 1 then
    bar_count = bar_count + 1
    bar_in_phrase = (bar_in_phrase % phrase_length) + 1

    -- Phrase boundary: mutate + maybe fill
    if bar_in_phrase == 1 and bar_count > 1 then
      mutate_pattern()
      if math.random(100) <= fill_probability then
        generate_fill()
      end
    end
  end

  -- Advance the arc
  advance_arc()

  -- Determine what to play
  local step_data

  if fill_active and fill_steps_remaining > 0 then
    local fill_idx = #fill_data - fill_steps_remaining + 1
    step_data = fill_data[fill_idx]
    fill_steps_remaining = fill_steps_remaining - 1
    if fill_steps_remaining <= 0 then
      fill_active = false
    end
  else
    step_data = live_patterns[current_bank][current_step]
  end

  -- Apply swing
  if swing_amount > 0 and current_step % 2 == 0 then
    local swing_delay = (swing_amount / 100) * (clock.get_beat_sec() / 8)
    clock.run(function()
      clock.sleep(swing_delay)
      note_on(step_data)
    end)
  else
    note_on(step_data)
  end

  screen_dirty = true
  grid_dirty = true
end

----------------------------------------------------------------
-- LATTICE
----------------------------------------------------------------

local function init_lattice()
  my_lattice = lattice_lib:new{}
  seq_sprocket = my_lattice:new_sprocket{
    action = step_advance,
    division = 1/16,
    enabled = true
  }
end

----------------------------------------------------------------
-- PARAMS
----------------------------------------------------------------

local function init_params()
  params:add_separator("SUBLIFE")

  params:add_group("GROOVE", 6)
  params:add_number("pocket_lock", "pocket lock", 0, 100, pocket_lock)
  params:set_action("pocket_lock", function(v) pocket_lock = v; screen_dirty = true end)
  params:add_number("mutation_rate", "mutation rate", 0, 100, mutation_rate)
  params:set_action("mutation_rate", function(v) mutation_rate = v; screen_dirty = true end)
  params:add_number("swing_amount", "swing", 0, 100, swing_amount)
  params:set_action("swing_amount", function(v) swing_amount = v; screen_dirty = true end)
  params:add_number("fill_probability", "fill probability", 0, 100, fill_probability)
  params:set_action("fill_probability", function(v) fill_probability = v; screen_dirty = true end)
  params:add_number("phrase_length", "phrase length", 1, 16, phrase_length)
  params:set_action("phrase_length", function(v) phrase_length = v; screen_dirty = true end)
  params:add_number("pattern_length", "pattern length", 1, 16, pattern_length)
  params:set_action("pattern_length", function(v) pattern_length = v; screen_dirty = true end)

  params:add_group("SOUND", 9)
  params:add_number("root_note", "root note", 24, 60, root_note)
  params:set_action("root_note", function(v)
    root_note = v; build_scale(); screen_dirty = true
  end)
  params:add_option("scale_type", "scale", SCALE_NAMES, scale_type)
  params:set_action("scale_type", function(v)
    scale_type = v; build_scale(); screen_dirty = true
  end)
  params:add_control("cutoff", "cutoff",
    controlspec.new(30, 16000, 'exp', 0, 800, "hz"))
  params:set_action("cutoff", function(v) engine.cutoff(v); screen_dirty = true end)
  params:add_control("resonance", "resonance",
    controlspec.new(0, 1, 'lin', 0, 0.3))
  params:set_action("resonance", function(v) engine.resonance(v) end)
  params:add_control("drive", "drive",
    controlspec.new(0, 1, 'lin', 0, 0.3))
  params:set_action("drive", function(v) engine.drive(v) end)
  params:add_control("sub_mix", "sub mix",
    controlspec.new(0, 1, 'lin', 0, 0.7))
  params:set_action("sub_mix", function(v) engine.sub_mix(v) end)
  params:add_control("saw_mix", "saw mix",
    controlspec.new(0, 1, 'lin', 0, 0.6))
  params:set_action("saw_mix", function(v) engine.saw_mix(v) end)
  params:add_control("filt_env_amt", "filter env",
    controlspec.new(0, 8000, 'exp', 0, 3000, "hz"))
  params:set_action("filt_env_amt", function(v) engine.filt_env_amt(v) end)
  params:add_control("slide_time", "slide time",
    controlspec.new(0.01, 0.5, 'exp', 0, 0.05, "s"))
  params:set_action("slide_time", function(v) engine.slide_time(v) end)

  params:add_group("ARCS", 4)
  params:add_number("arc_speed", "arc speed (bars)", 1, 64, arc_speed)
  params:set_action("arc_speed", function(v) arc_speed = v; screen_dirty = true end)
  params:add_option("arc_shape", "arc shape", ARC_SHAPES, arc_shape)
  params:set_action("arc_shape", function(v) arc_shape = v; screen_dirty = true end)
  params:add_control("arc_depth", "arc depth",
    controlspec.new(0, 1, 'lin', 0, 0.6))
  params:set_action("arc_depth", function(v) arc_depth = v; screen_dirty = true end)
  params:add_control("amp_dec", "amp decay",
    controlspec.new(0.01, 2.0, 'exp', 0, 0.2, "s"))
  params:set_action("amp_dec", function(v) engine.amp_dec(v) end)

  params:add_group("MIX", 2)
  params:add_control("comp_thresh", "comp threshold",
    controlspec.new(0.1, 1, 'lin', 0, 0.6))
  params:set_action("comp_thresh", function(v) engine.comp_thresh(v) end)
  params:add_control("comp_ratio", "comp ratio",
    controlspec.new(1, 10, 'lin', 0, 3))
  params:set_action("comp_ratio", function(v) engine.comp_ratio(v) end)
end

----------------------------------------------------------------
-- GRID
----------------------------------------------------------------

local grid_dirty = true

local function grid_redraw()
  if not g.device then return end
  g:all(0)

  local pat = live_patterns[current_bank]

  -- Rows 1-6: Piano roll
  for col = 1, pattern_length do
    local sd = pat[col]
    for row = 1, GRID_PITCH_ROWS do
      -- row 1 = highest pitch, row 6 = lowest
      local pitch_idx = GRID_PITCH_ROWS - row + 1 -- 6,5,4,3,2,1
      local target_note = scale_notes[pitch_idx] or (root_note + (pitch_idx - 1) * 2)

      local brightness = BRIGHT.OFF

      -- dim grid for reference
      if col <= pattern_length then
        brightness = BRIGHT.GHOST
      end

      -- show note
      if sd.note > 0 and sd.artic ~= ARTIC.REST then
        local note_pitch_idx = find_scale_index(sd.note, scale_notes)
        -- map to grid row range
        local note_row = GRID_PITCH_ROWS - clamp(note_pitch_idx, 1, GRID_PITCH_ROWS) + 1
        if row == note_row then
          if sd.artic == ARTIC.GHOST then
            brightness = BRIGHT.DIM
          elseif sd.accent then
            brightness = BRIGHT.FULL
          else
            brightness = BRIGHT.MID + math.floor(sd.vel / 127 * 4)
          end
        end
      end

      -- playhead
      if col == current_step and playing then
        if brightness > BRIGHT.GHOST then
          brightness = BRIGHT.FULL
        else
          brightness = BRIGHT.DIM
        end
      end

      g:led(col, row, clamp(brightness, 0, 15))
    end
  end

  -- Row 7: Accent pattern
  for col = 1, pattern_length do
    local sd = pat[col]
    local brightness = BRIGHT.OFF
    if sd.accent then
      brightness = BRIGHT.BRIGHT
    elseif sd.note > 0 and sd.artic ~= ARTIC.REST then
      brightness = BRIGHT.DIM
    end
    if col == current_step and playing then
      brightness = math.max(brightness, BRIGHT.MID)
    end
    g:led(col, GRID_ACCENT_ROW, brightness)
  end

  -- Row 8: Controls
  -- Col 1-4: bank select
  for i = 1, NUM_BANKS do
    g:led(i, GRID_CTRL_ROW, i == current_bank and BRIGHT.FULL or BRIGHT.DIM)
  end
  -- Col 6: mutate
  g:led(6, GRID_CTRL_ROW, BRIGHT.MID)
  -- Col 7: reset
  g:led(7, GRID_CTRL_ROW, BRIGHT.MID)
  -- Col 8: capture
  g:led(8, GRID_CTRL_ROW, BRIGHT.MID)
  -- Col 10-13: variation amount (4-step fader)
  local var_level = math.floor((100 - pocket_lock) / 25) + 1 -- 1-5
  for i = 10, 13 do
    local lvl = i - 9
    g:led(i, GRID_CTRL_ROW, lvl <= var_level and BRIGHT.BRIGHT or BRIGHT.GHOST)
  end
  -- Col 15: fill trigger
  g:led(15, GRID_CTRL_ROW, fill_active and BRIGHT.FULL or BRIGHT.DIM)
  -- Col 16: play/stop
  g:led(16, GRID_CTRL_ROW, playing and BRIGHT.FULL or BRIGHT.MID)

  g:refresh()
end

g.key = function(x, y, z)
  if z == 0 then return end -- only act on press

  local pat = live_patterns[current_bank]
  local home = home_patterns[current_bank]

  if y >= 1 and y <= GRID_PITCH_ROWS then
    -- Piano roll: toggle note at this pitch
    local pitch_idx = GRID_PITCH_ROWS - y + 1
    local target_note = scale_notes[pitch_idx] or (root_note + (pitch_idx - 1) * 2)

    if x >= 1 and x <= pattern_length then
      local sd = pat[x]
      local hd = home[x]
      if sd.note == target_note then
        -- toggle off
        sd.note = 0; sd.artic = ARTIC.REST; sd.vel = 0
        hd.note = 0; hd.artic = ARTIC.REST; hd.vel = 0
      else
        -- set note
        sd.note = target_note
        sd.vel = 100
        sd.dur = 0.5
        sd.artic = ARTIC.PLUCK
        sd.prob = 100
        -- also set home
        hd.note = target_note
        hd.vel = 100
        hd.dur = 0.5
        hd.artic = ARTIC.PLUCK
        hd.prob = 100
      end
    end
  elseif y == GRID_ACCENT_ROW then
    -- Toggle accent
    if x >= 1 and x <= pattern_length then
      pat[x].accent = not pat[x].accent
      home[x].accent = pat[x].accent
      if pat[x].accent then
        pat[x].vel = 127
        home[x].vel = 127
      else
        pat[x].vel = 100
        home[x].vel = 100
      end
    end
  elseif y == GRID_CTRL_ROW then
    if x >= 1 and x <= NUM_BANKS then
      -- Bank select
      current_bank = x
    elseif x == 6 then
      -- Mutate
      force_mutate()
    elseif x == 7 then
      -- Reset
      reset_to_home()
    elseif x == 8 then
      -- Capture
      capture_to_home()
    elseif x >= 10 and x <= 13 then
      -- Variation amount fader
      local level = x - 9 -- 1-4
      pocket_lock = 100 - (level * 25)
      params:set("pocket_lock", pocket_lock)
    elseif x == 15 then
      -- Trigger fill now
      generate_fill()
    elseif x == 16 then
      -- Play/stop
      if playing then
        playing = false
        engine.note_off()
        current_step = 0
      else
        playing = true
        current_step = 0
        bar_count = 0
        bar_in_phrase = 0
        my_lattice:hard_restart()
      end
    end
  end

  screen_dirty = true
  grid_dirty = true
end

----------------------------------------------------------------
-- SCREEN
----------------------------------------------------------------

local function draw_pattern_viz()
  -- Draw the live pattern as a mini piano roll
  local pat = live_patterns[current_bank]
  local x_start = 2
  local x_width = 7 -- pixels per step
  local y_top = 2
  local y_bottom = 38
  local pitch_range = 36 -- semitones visible

  for s = 1, pattern_length do
    local sd = pat[s]
    local x = x_start + (s - 1) * x_width

    -- Playhead column
    if s == current_step and playing then
      screen.level(2)
      screen.rect(x, y_top, x_width - 1, y_bottom - y_top)
      screen.fill()
    end

    if sd.note > 0 and sd.artic ~= ARTIC.REST then
      -- Map note to y position
      local note_offset = sd.note - (root_note - 12)
      local y = y_bottom - (note_offset / pitch_range) * (y_bottom - y_top)
      y = clamp(y, y_top, y_bottom - 2)

      -- Brightness based on velocity and articulation
      local level = math.floor(sd.vel / 127 * 12) + 3
      if sd.artic == ARTIC.GHOST then level = math.floor(level * 0.4) end
      if sd.accent then level = 15 end
      if s == current_step and playing then level = 15 end
      screen.level(clamp(level, 1, 15))

      -- Draw note dot
      local dot_size = sd.artic == ARTIC.SLAP and 3 or 2
      if sd.artic == ARTIC.MUTE then
        -- muted notes: hollow
        screen.rect(x + 1, y, dot_size, dot_size)
        screen.stroke()
      else
        screen.rect(x + 1, y, dot_size, dot_size)
        screen.fill()
      end

      -- Slide indicator: small line down
      if sd.artic == ARTIC.SLIDE then
        screen.move(x + 2, y + 2)
        screen.line(x + 2, y + 5)
        screen.stroke()
      end
    end
  end

  -- Arc visualization: thin bar at bottom of viz area
  screen.level(4)
  local arc_x = x_start + arc_phase * (pattern_length * x_width - 2)
  screen.rect(arc_x, y_bottom + 1, 2, 2)
  screen.fill()
end

local function draw_params()
  local y_start = 44
  local pg = param_pages[page]
  if not pg then return end

  -- Page indicator
  screen.level(4)
  screen.move(2, y_start)
  local page_names = { "GROOVE", "SOUND", "ARCS" }
  screen.text(page_names[page])

  -- Show 2 params (selected and next)
  for i = 0, 1 do
    local idx = selected_param + i
    if idx > #pg then break end
    local p = pg[idx]
    local y = y_start + 8 + (i * 10)

    -- Name
    screen.level(i == 0 and 15 or 4)
    screen.move(2, y)
    screen.text(p.name)

    -- Value
    screen.move(126, y)
    screen.text_right(string.format("%.0f", params:get(p.key) or 0))
  end
end

function redraw()
  screen.clear()

  -- Status bar
  screen.level(playing and 15 or 4)
  screen.move(2, 62)
  screen.text(playing and "▶" or "■")

  screen.level(8)
  screen.move(12, 62)
  screen.text("BK:" .. current_bank)

  screen.move(38, 62)
  screen.text("S:" .. current_step)

  if fill_active then
    screen.level(15)
    screen.move(60, 62)
    screen.text("FILL")
  end

  screen.level(6)
  screen.move(86, 62)
  screen.text("PL:" .. pocket_lock)

  -- Pattern visualization
  draw_pattern_viz()

  -- Parameters
  draw_params()

  screen.update()
end

----------------------------------------------------------------
-- INPUT
----------------------------------------------------------------

function enc(n, d)
  if n == 1 then
    -- ENC1: pocket lock
    pocket_lock = clamp(pocket_lock + d, 0, 100)
    params:set("pocket_lock", pocket_lock)
  elseif n == 2 then
    -- ENC2: navigate params / pages
    -- hold KEY1 to change pages (not implemented for simplicity, use long press)
    local pg = param_pages[page]
    if pg then
      selected_param = clamp(selected_param + d, 1, #pg)
    end
  elseif n == 3 then
    -- ENC3: adjust selected param
    local pg = param_pages[page]
    if pg and pg[selected_param] then
      params:delta(pg[selected_param].key, d)
    end
  end
  screen_dirty = true
end

function key(n, z)
  if n == 2 then
    if z == 1 then
      -- Play/Stop
      if playing then
        playing = false
        engine.note_off()
        current_step = 0
      else
        playing = true
        current_step = 0
        bar_count = 0
        bar_in_phrase = 0
        my_lattice:hard_restart()
      end
    end
  elseif n == 3 then
    if z == 1 then
      key3_time = util.time()
    else
      -- Release
      local held = util.time() - key3_time
      if held > 1.0 then
        -- Long hold: reset to home
        reset_to_home()
      elseif held > 0.5 then
        -- Medium hold: change page
        page = (page % #param_pages) + 1
        selected_param = 1
      else
        -- Short tap: mutate
        force_mutate()
      end
    end
  end
  screen_dirty = true
end

----------------------------------------------------------------
-- SCREEN REFRESH CLOCK
----------------------------------------------------------------

local function screen_refresh()
  while true do
    clock.sleep(1/15)
    if screen_dirty then
      redraw()
      screen_dirty = false
    end
    if grid_dirty then
      grid_redraw()
      grid_dirty = false
    end
  end
end

----------------------------------------------------------------
-- INIT
----------------------------------------------------------------

function init()
  build_scale()
  init_patterns()
  init_params()
  init_lattice()
  my_lattice:start()
  clock.run(screen_refresh)

  -- Grid connect callback
  g.key = g.key -- already set above
  grid_redraw()
  redraw()
end

function cleanup()
  if my_lattice then my_lattice:destroy() end
end
