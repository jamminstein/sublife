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
-- v1.2 - redesigned screen with zone system, melodic contour, tension arc

engine.name = "Sublife"

local musicutil = require "musicutil"
local lattice_lib = require "lattice"

local grid_dirty = true

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
local m = nil
local my_lattice
local seq_sprocket
local metro_redraw

local playing = false
local screen_clock_id = nil
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

-- arc system (long-form macro parameter sweeps)
local arc_phase = 0
local arc_speed = 4        -- how many bars per full arc cycle
local arc_shape = 1        -- index into ARC_SHAPES
local arc_depth = 0.6      -- 0-1, how much the arc affects cutoff
local arc_cutoff_min = 150
local arc_cutoff_max = 5000
local arc_drift_val = 0.5  -- random walk state

-- reference artist style system
local style = "custom"     -- "lcd", "flea", "daft", "custom"
local STYLE_PRESETS = {
  lcd = {density=0.7, range=12, staccato=0.3},
  flea = {density=0.85, range=24, staccato=0.1},
  daft = {density=0.6, range=8, staccato=0.5}
}

-- drive/compression
local drive = 0.0          -- 0.0-1.0, velocity boost for aggressive bass

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

-- TENSION ARC SYSTEM
local tension = 0.0         -- 0.0-1.0, builds over time
local tension_speed = 0.02  -- how fast tension builds per bar
local tension_mode = true   -- auto-reset vs manual control
local drop_flash = 0        -- time remaining for drop flash (0 = no flash)
local drop_flash_duration = 0.2

-- CALL-AND-RESPONSE SYSTEM
local call_buffer = {}      -- stores incoming MIDI notes
local call_active = false
local response_pending = false

-- OP-XY MIDI
local opxy_out = nil
local opxy_enabled = false
local opxy_device = 1
local opxy_channel = 2  -- OP-XY bass channel

local function opxy_note_on(note, vel)
  if opxy_out and opxy_enabled then
    opxy_out:note_on(note, vel, opxy_channel)
  end
end

local function opxy_note_off(note)
  if opxy_out and opxy_enabled then
    opxy_out:note_off(note, 0, opxy_channel)
  end
end

local function opxy_cc(cc_num, val)
  if opxy_out and opxy_enabled then
    opxy_out:cc(cc_num, math.floor(util.clamp(val, 0, 127)), opxy_channel)
  end
end

local function opxy_all_notes_off()
  if opxy_out and opxy_enabled then
    opxy_out:cc(123, 0, opxy_channel)
  end
end

-- screen state
local screen_dirty = true
local selected_param = 1
local page = 1 -- 1=main, 2=sound, 3=arcs
local beat_phase = 0        -- 0-1 for beat pulse animation
local popup_param = nil     -- currently showing parameter popup
local popup_val = nil
local popup_time = 0        -- countdown to hide popup

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

-- MIDI sync
local clock_source = "internal"  -- "internal" or "midi"
local midi_clock_count = 0
local external_bpm = 120

-- phrase boundary flash
local phrase_flash = 0  -- time remaining for flash (0 = no flash)

-- markov chain for note transitions (scale degree transitions)
local markov = {
  { 30, 10, 15, 5, 20, 10, 10 },
  { 25, 10, 20, 10, 10, 15, 10 },
  { 20, 15, 10, 20, 10, 10, 15 },
  { 15, 10, 20, 10, 20, 15, 10 },
  { 25, 10, 10, 15, 10, 15, 15 },
  { 20, 15, 10, 10, 20, 10, 15 },
  { 30, 10, 15, 10, 15, 10, 10 },
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
-- TENSION SYSTEM
----------------------------------------------------------------

local function update_tension()
  if tension_mode then
    -- Auto-increment tension
    tension = tension + tension_speed
    if tension >= 1.0 then
      -- Auto-reset at peak (simulates "drop")
      tension = 0.0
      drop_flash = drop_flash_duration
    end
  end
end

local function get_tension_density()
  -- Higher tension = more notes
  return 0.3 + tension * 0.6
end

local function get_tension_octave_range()
  -- Higher tension = wider range
  return math.floor(2 + tension * 4)
end

----------------------------------------------------------------
-- CALL-AND-RESPONSE SYSTEM
----------------------------------------------------------------

local function init_midi()
  m = midi.connect(1)
  if m then
    m.event = function(data)
      local msg = midi.to_msg(data)

      -- MIDI clock sync
      if msg.type == "clock" and clock_source == "midi" then
        midi_clock_count = (midi_clock_count + 1) % 24  -- 24 clocks per quarter note
        if midi_clock_count == 0 and playing then
          -- trigger step advance on quarter note boundaries
          step_advance()
        end
      elseif msg.type == "start" then
        if clock_source == "midi" and not playing then
          playing = true
          current_step = 0
          bar_count = 0
          bar_in_phrase = 0
          midi_clock_count = 0
        end
      elseif msg.type == "stop" then
        if clock_source == "midi" then
          playing = false
          engine.note_off()
          current_step = 0
        end
      end

      -- Call-and-response system
      if msg.type == "note_on" and msg.vel > 0 then
        table.insert(call_buffer, msg.note)
        call_active = true
      elseif msg.type == "note_off" or (msg.type == "note_on" and msg.vel == 0) then
        -- Mark response as pending for next pattern cycle
        if #call_buffer > 0 then
          response_pending = true
        end
      end
    end
  end
end

local function generate_response()
  if #call_buffer == 0 then return end
  
  -- Generate complementary notes based on call notes
  for i = 1, pattern_length do
    local live = live_patterns[current_bank][i]
    if math.random() < 0.4 then
      -- Pick a note relative to a call note
      local call_note = call_buffer[((i - 1) % #call_buffer) + 1]
      local scale_idx = find_scale_index(call_note, scale_notes)
      if scale_idx then
        -- Generate a response using scale intervals
        local intervals = {0, 3, 5, 7, -2, -5}  -- complementary intervals
        local interval_idx = ((i - 1) % #intervals) + 1
        local response_idx = clamp(scale_idx + intervals[interval_idx], 1, #scale_notes)
        live.note = scale_notes[response_idx]
        live.vel = 80 + math.random(0, 30)
        live.artic = ARTIC.PLUCK
        live.prob = 100
      end
    end
  end
  
  call_buffer = {}
  response_pending = false
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
    note   = 0,
    vel    = 100,
    dur    = 0.5,
    artic  = ARTIC.PLUCK,
    prob   = 100,
    accent = false,
    micro  = 0,
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

function seed_groove(bank)
  local r = root_note
  local p5 = root_note + 7
  local m3 = root_note + 3
  local sub = root_note - 12
  local p = home_patterns[bank]

  p[1]  = { note=r,   vel=120, dur=0.8, artic=ARTIC.PLUCK, prob=100, accent=true,  micro=0 }
  p[2]  = { note=0,   vel=0,   dur=0,   artic=ARTIC.REST,  prob=100, accent=false, micro=0 }
  p[3]  = { note=r,   vel=40,  dur=0.3, artic=ARTIC.GHOST, prob=70,  accent=false, micro=0 }
  p[4]  = { note=0,   vel=0,   dur=0,   artic=ARTIC.REST,  prob=100, accent=false, micro=0 }
  p[5]  = { note=p5,  vel=110, dur=0.5, artic=ARTIC.SLAP,  prob=100, accent=false, micro=0 }
  p[6]  = { note=r,   vel=35,  dur=0.2, artic=ARTIC.GHOST, prob=55,  accent=false, micro=0 }
  p[7]  = { note=0,   vel=0,   dur=0,   artic=ARTIC.REST,  prob=100, accent=false, micro=0 }
  p[8]  = { note=m3,  vel=60,  dur=0.3, artic=ARTIC.MUTE,  prob=80,  accent=false, micro=0 }
  p[9]  = { note=r,   vel=115, dur=0.7, artic=ARTIC.PLUCK, prob=100, accent=true,  micro=0 }
  p[10] = { note=0,   vel=0,   dur=0,   artic=ARTIC.REST,  prob=100, accent=false, micro=0 }
  p[11] = { note=r,   vel=45,  dur=0.25,artic=ARTIC.GHOST, prob=65,  accent=false, micro=0 }
  p[12] = { note=r+5, vel=70,  dur=0.4, artic=ARTIC.SLIDE, prob=75,  accent=false, micro=0 }
  p[13] = { note=p5,  vel=105, dur=0.5, artic=ARTIC.PLUCK, prob=95,  accent=false, micro=0 }
  p[14] = { note=r,   vel=30,  dur=0.2, artic=ARTIC.GHOST, prob=50,  accent=false, micro=0 }
  p[15] = { note=sub, vel=95,  dur=0.5, artic=ARTIC.PLUCK, prob=85,  accent=false, micro=0 }
  p[16] = { note=r-1, vel=65,  dur=0.3, artic=ARTIC.SLIDE, prob=70,  accent=false, micro=0 }

  for s = 1, NUM_STEPS do
    live_patterns[bank][s] = deep_copy(home_patterns[bank][s])
  end
end

----------------------------------------------------------------
-- MUTATION ENGINE
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
      if step_data.note == 0 then
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
      if step_data.note == 0 then return end
      local idx = find_scale_index(step_data.note, scale_notes)
      local degree = ((idx - 1) % 7) + 1
      local next_degree = weighted_choice(markov[degree])
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

  local mutation_chance = (100 - pocket_lock) * mutation_rate / 100 / 100

  if math.random() > mutation_chance then
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

  local weights = {}
  for _, m in ipairs(mutation_types) do
    table.insert(weights, m.weight)
  end
  local choice = weighted_choice(weights)
  mutation_types[choice].fn(live)
end

local function mutate_pattern()
  for s = 1, pattern_length do
    mutate_step(s)
  end
  screen_dirty = true
end

local function force_mutate()
  local saved_lock = pocket_lock
  pocket_lock = math.max(0, pocket_lock - 40)
  for s = 1, pattern_length do
    mutate_step(s)
    mutate_step(s)
  end
  pocket_lock = saved_lock
  screen_dirty = true
end

local function reset_to_home()
  for s = 1, NUM_STEPS do
    live_patterns[current_bank][s] = deep_copy(home_patterns[current_bank][s])
  end
  screen_dirty = true
end

local function capture_to_home()
  for s = 1, NUM_STEPS do
    home_patterns[current_bank][s] = deep_copy(live_patterns[current_bank][s])
  end
  screen_dirty = true
end

----------------------------------------------------------------
-- ARC SYSTEM
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

  local av = arc_value()
  local cutoff = arc_cutoff_min + (arc_cutoff_max - arc_cutoff_min) * av * arc_depth
  cutoff = cutoff + arc_cutoff_min * (1 - arc_depth)
  engine.cutoff(cutoff)
end

----------------------------------------------------------------
-- FILL SYSTEM
----------------------------------------------------------------

local function generate_fill()
  fill_data = {}
  local fill_type = math.random(1, 5)
  local fill_len = math.random(2, 6)

  if fill_type == 1 then
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
    for i = 1, fill_len do
      fill_data[i] = {
        note = 0,
        vel = 0,
        dur = 0,
        artic = ARTIC.REST,
      }
    end
  elseif fill_type == 5 then
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

  if math.random(100) > step_data.prob then return end

  local freq = musicutil.note_num_to_freq(step_data.note)
  local vel = step_data.vel / 127

  -- Apply drive/compression for velocity boost
  if drive > 0 then
    vel = vel * (1 + drive * 0.5)
    vel = clamp(vel, 0, 1.0)  -- clamped to normalize
  end

  local cutoff = params:get("cutoff")
  local artic = step_data.artic
  local slide = params:get("slide_time")

  engine.note_on(freq, vel, cutoff, artic, slide)
  opxy_note_on(step_data.note, step_data.vel)

  local step_dur = clock.get_beat_sec() / 4
  clock.run(function()
    clock.sleep(step_dur * step_data.dur)
    engine.note_off()
    opxy_note_off(step_data.note)
  end)
end

local function step_advance()
  if not playing then return end

  current_step = (current_step % pattern_length) + 1

  if current_step == 1 then
    bar_count = bar_count + 1
    bar_in_phrase = (bar_in_phrase % phrase_length) + 1

    if bar_in_phrase == 1 and bar_count > 1 then
      mutate_pattern()
      update_tension()
      if math.random(100) <= fill_probability then
        generate_fill()
      end
      -- Phrase boundary flash
      phrase_flash = 0.3  -- flash duration
    end

    -- Check for pending call-and-response
    if response_pending then
      generate_response()
    end
  end

  advance_arc()

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

  if swing_amount > 0 and current_step % 2 == 0 then
    local swing_delay = (swing_amount / 100) * (clock.get_beat_sec() / 8)
    clock.run(function()
      clock.sleep(swing_delay)
      note_on(step_data)
    end)
  else
    note_on(step_data)
  end

  -- Send OP-XY envelope and level CCs
  local filt_env = params:get("filt_env_amt") or 0
  opxy_cc(24, util.linlin(0, 8000, 0, 127, filt_env))  -- Filter env attack
  opxy_cc(51, util.linlin(0, 1, 0, 127, params:get("sub_mix") or 0.7))  -- Level/mix

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

  params:add_group("SOUND", 11)
  params:add_option("style", "artist mode", {"lcd", "flea", "daft", "custom"}, 4)
  params:set_action("style", function(v)
    style = ({"lcd", "flea", "daft", "custom"})[v]
    if STYLE_PRESETS[style] then
      local preset = STYLE_PRESETS[style]
      -- Apply preset parameters
      pocket_lock = 100 - (preset.density * 30)  -- convert density to variation
      local range_idx = clamp(math.floor(preset.range / 4), 1, 7)
    end
    screen_dirty = true
  end)
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
    controlspec.new(0, 1, 'lin', 0, 0.0))
  params:set_action("drive", function(v) drive = v; screen_dirty = true end)
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

  params:add_group("ARCS", 5)
  params:add_option("clock_source", "clock", {"internal", "midi"}, 1)
  params:set_action("clock_source", function(v)
    clock_source = v == 1 and "internal" or "midi"
    screen_dirty = true
  end)
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

  params:add_group("OP-XY", 3)
  params:add_option("opxy_enabled", "OP-XY output", {"off", "on"}, 1)
  params:set_action("opxy_enabled", function(x) 
    opxy_enabled = (x == 2)
    if opxy_out == nil then
      opxy_out = midi.connect(params:get("opxy_device"))
    end
  end)
  params:add_number("opxy_device", "OP-XY MIDI device", 1, 4, 1)
  params:set_action("opxy_device", function(val)
    opxy_out = midi.connect(val)
  end)
  params:add_number("opxy_channel", "OP-XY channel", 1, 8, 2)
  params:set_action("opxy_channel", function(x) opxy_channel = x end)
end

----------------------------------------------------------------
-- GRID
----------------------------------------------------------------

local function grid_redraw()
  if not g.device then return end
  g:all(0)

  local pat = live_patterns[current_bank]

  for col = 1, pattern_length do
    local sd = pat[col]
    for row = 1, GRID_PITCH_ROWS do
      local pitch_idx = GRID_PITCH_ROWS - row + 1
      local target_note = scale_notes[pitch_idx] or (root_note + (pitch_idx - 1) * 2)

      local brightness = BRIGHT.OFF

      if col <= pattern_length then
        brightness = BRIGHT.GHOST
      end

      if sd.note > 0 and sd.artic ~= ARTIC.REST then
        local note_pitch_idx = find_scale_index(sd.note, scale_notes)
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

  for i = 1, NUM_BANKS do
    g:led(i, GRID_CTRL_ROW, i == current_bank and BRIGHT.FULL or BRIGHT.DIM)
  end
  g:led(6, GRID_CTRL_ROW, BRIGHT.MID)
  g:led(7, GRID_CTRL_ROW, BRIGHT.MID)
  g:led(8, GRID_CTRL_ROW, BRIGHT.MID)
  
  local var_level = math.floor((100 - pocket_lock) / 25) + 1
  for i = 10, 13 do
    local lvl = i - 9
    g:led(i, GRID_CTRL_ROW, lvl <= var_level and BRIGHT.BRIGHT or BRIGHT.GHOST)
  end
  g:led(15, GRID_CTRL_ROW, fill_active and BRIGHT.FULL or BRIGHT.DIM)
  g:led(16, GRID_CTRL_ROW, playing and BRIGHT.FULL or BRIGHT.MID)

  g:refresh()
end

g.key = function(x, y, z)
  if z == 0 then return end

  local pat = live_patterns[current_bank]
  local home = home_patterns[current_bank]

  if y >= 1 and y <= GRID_PITCH_ROWS then
    local pitch_idx = GRID_PITCH_ROWS - y + 1
    local target_note = scale_notes[pitch_idx] or (root_note + (pitch_idx - 1) * 2)

    if x >= 1 and x <= pattern_length then
      local sd = pat[x]
      local hd = home[x]
      if sd.note == target_note then
        sd.note = 0; sd.artic = ARTIC.REST; sd.vel = 0
        hd.note = 0; hd.artic = ARTIC.REST; hd.vel = 0
      else
        sd.note = target_note
        sd.vel = 100
        sd.dur = 0.5
        sd.artic = ARTIC.PLUCK
        sd.prob = 100
        hd.note = target_note
        hd.vel = 100
        hd.dur = 0.5
        hd.artic = ARTIC.PLUCK
        hd.prob = 100
      end
    end
  elseif y == GRID_ACCENT_ROW then
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
      current_bank = x
    elseif x == 6 then
      force_mutate()
    elseif x == 7 then
      reset_to_home()
    elseif x == 8 then
      capture_to_home()
    elseif x >= 10 and x <= 13 then
      local level = x - 9
      pocket_lock = 100 - (level * 25)
      params:set("pocket_lock", pocket_lock)
    elseif x == 15 then
      generate_fill()
    elseif x == 16 then
      if playing then
        playing = false
        engine.note_off()
        opxy_all_notes_off()
        current_step = 0
      else
        playing = true
        current_step = 0
        bar_count = 0
        bar_in_phrase = 0
        if my_lattice then
          my_lattice:hard_restart()
        end
      end
    end
  end

  screen_dirty = true
  grid_dirty = true
end

----------------------------------------------------------------
-- SCREEN - NEW ZONE-BASED DESIGN
----------------------------------------------------------------

local function draw_status_strip()
  -- ZONE 1: y 0-8
  -- Left: "SUBLIFE" title at level 4
  screen.level(4)
  screen.move(2, 6)
  screen.text("SUBLIFE")

  -- Center: Current mutation mode at level 6
  local mode_name = "LIVE"
  if fill_active then mode_name = "FILL" end
  screen.level(6)
  screen.move(64, 6)
  screen.text_center(mode_name)

  -- Right: Beat pulse dot at x=124 (flashes on beat)
  local pulse_level = 6 + math.floor(beat_phase * 9)
  screen.level(pulse_level)
  screen.rect(124, 4, 2, 2)
  screen.fill()
end

local function draw_live_zone()
  -- ZONE 2: y 9-52
  -- Draw 16-step bass sequence as melodic contour
  local pat = live_patterns[current_bank]

  local x_start = 2
  local x_step = 8
  local y_top = 10
  local y_bottom = 48
  local pitch_range = 36

  -- Phrase boundary flash indicator
  if phrase_flash > 0 then
    phrase_flash = phrase_flash - (1/12)
    local flash_level = math.floor(phrase_flash * 15)
    screen.level(flash_level)
    screen.rect(0, y_top - 2, 128, 4)
    screen.fill()
  end

  -- Points for contour line
  local points = {}

  for s = 1, pattern_length do
    local sd = pat[s]
    local x = x_start + (s - 1) * x_step

    if sd.note > 0 and sd.artic ~= ARTIC.REST then
      local note_offset = sd.note - (root_note - 12)
      local y = y_bottom - (note_offset / pitch_range) * (y_bottom - y_top)
      y = clamp(y, y_top, y_bottom - 2)

      table.insert(points, {x = x, y = y, step = s, data = sd})
    end
  end
  
  -- Draw contour line with antialiasing
  if #points > 1 then
    screen.level(8)
    screen.aa(0)
    for i = 1, #points - 1 do
      screen.move(points[i].x, points[i].y)
      screen.line(points[i + 1].x, points[i + 1].y)
    end
    screen.stroke()
    screen.aa(0)
  end
  
  -- Draw note dots (playhead and active steps)
  for _, p in ipairs(points) do
    local level = 12  -- default active step
    local size = 2

    if p.step == current_step and playing then
      level = 15  -- playhead is brightest
    end

    if p.data.artic == ARTIC.GHOST then
      level = 6   -- ghost notes are dim
      size = 1
    elseif p.data.accent then
      level = 15  -- accents are bright
      size = 3
    end

    screen.level(level)
    screen.rect(p.x - size/2, p.y - size/2, size, size)
    screen.fill()
  end

  -- Draw phrase boundary marker (▸) at phrase positions
  if bar_in_phrase == 1 and bar_count > 0 then
    screen.level(8)
    screen.move(2, y_bottom + 5)
    screen.text("▸")  -- right-pointing triangle at phrase start
  end
  
  -- TENSION ARC: thin horizontal bar at y ~48-50
  local tension_bar_y = 48
  local tension_bar_h = 2
  
  local tension_level = 6 + math.floor(tension * 6)  -- 6-12 normally
  if drop_flash > 0 then
    tension_level = 15  -- flash bright on drop
    drop_flash = drop_flash - (1/12)  -- decrement by frame
  end
  
  screen.level(tension_level)
  local tension_width = math.floor(pattern_length * x_step * tension)
  screen.rect(x_start, tension_bar_y, tension_width, tension_bar_h)
  screen.fill()
  
  -- MUTATION PREVIEW: show dim alternate note for next mutation
  if pocket_lock < 80 then  -- only show when locked enough to be interesting
    local preview_step = ((current_step % pattern_length) + 1)
    if preview_step <= pattern_length then
      local sd = pat[preview_step]
      if sd.note > 0 and sd.artic ~= ARTIC.REST then
        local note_offset = sd.note - (root_note - 12)
        local y = y_bottom - (note_offset / pitch_range) * (y_bottom - y_top)
        y = clamp(y, y_top, y_bottom - 2)
        
        -- show predicted alternative 2 semitones up
        local alt_offset = note_offset + 2
        local alt_y = y_bottom - (alt_offset / pitch_range) * (y_bottom - y_top)
        alt_y = clamp(alt_y, y_top, y_bottom - 2)
        
        local x = x_start + (preview_step - 1) * x_step
        screen.level(3)  -- very dim preview
        screen.rect(x - 1, alt_y - 1, 2, 2)
        screen.fill()
      end
    end
  end
end

local function draw_context_bar()
  -- ZONE 3: y 53-58
  local y = 54
  
  -- Root + Scale at level 8
  screen.level(8)
  screen.move(2, y)
  local note_name = musicutil.note_num_to_name(root_note)
  screen.text(note_name .. " " .. SCALE_NAMES[scale_type]:sub(1, 3))
  
  -- BPM at level 6
  screen.level(6)
  screen.move(50, y)
  screen.text("BPM: " .. math.floor(params:get("arc_speed")))
  
  -- Mutation rate at level 5
  screen.level(5)
  screen.move(86, y)
  screen.text("MUT: " .. math.floor(mutation_rate))
  
  -- "DROP IN X" countdown at level 6 if tension building
  if tension > 0.5 then
    screen.level(6)
    local bars_until_drop = math.ceil((1.0 - tension) / tension_speed)
    screen.move(126, y)
    screen.text_right("DROP:" .. bars_until_drop)
  end
end

local function draw_popup()
  -- TRANSIENT PARAMETER POPUP: enc() triggers popup for 0.8s
  if popup_param and popup_time > 0 then
    popup_time = popup_time - (1/12)
    
    screen.level(15)
    screen.rect(32, 24, 64, 16)
    screen.fill()
    
    screen.level(0)
    screen.move(64, 28)
    screen.text_center(popup_param)
    
    screen.move(64, 38)
    screen.text_center(tostring(popup_val))
  end
end

function redraw()
  screen.clear()
  
  -- ~12fps refresh for tension animation and beat pulse
  beat_phase = (beat_phase + 1/12) % 1.0
  
  draw_status_strip()
  draw_live_zone()
  draw_context_bar()
  draw_popup()
  
  screen.update()
end

----------------------------------------------------------------
-- INPUT
----------------------------------------------------------------

function enc(n, d)
  if n == 1 then
    if not tension_mode then
      -- Manual tension control when alt held
      tension = clamp(tension + d * 0.02, 0.0, 1.0)
    else
      pocket_lock = clamp(pocket_lock + d, 0, 100)
      params:set("pocket_lock", pocket_lock)
      popup_param = "POCKET LOCK"
      popup_val = pocket_lock
      popup_time = 0.8
    end
  elseif n == 2 then
    local pg = param_pages[page]
    if pg then
      selected_param = clamp(selected_param + d, 1, #pg)
    end
  elseif n == 3 then
    local pg = param_pages[page]
    if pg and pg[selected_param] then
      params:delta(pg[selected_param].key, d)
      popup_param = pg[selected_param].name:upper()
      popup_val = params:get(pg[selected_param].key)
      popup_time = 0.8
    end
  end
  screen_dirty = true
end

function key(n, z)
  if n == 2 then
    if z == 1 then
      if playing then
        playing = false
        engine.note_off()
        opxy_all_notes_off()
        current_step = 0
      else
        playing = true
        current_step = 0
        bar_count = 0
        bar_in_phrase = 0
        if my_lattice then
          my_lattice:hard_restart()
        end
      end
    end
  elseif n == 3 then
    if z == 1 then
      key3_time = util.time()
    else
      local held = util.time() - key3_time
      if held > 1.0 then
        reset_to_home()
      elseif held > 0.5 then
        page = (page % #param_pages) + 1
        selected_param = 1
      else
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
    clock.sleep(1/12)  -- 12fps for smooth animation
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
  init_midi()
  if my_lattice then
    my_lattice:start()
  end
  screen_clock_id = clock.run(screen_refresh)

  g.key = g.key
  grid_redraw()
  redraw()
end

function cleanup()
  playing = false
  engine.note_off()
  opxy_all_notes_off()
  if my_lattice then
    my_lattice:destroy()
  end
  if screen_clock_id then clock.cancel(screen_clock_id) end
  if m then for ch=1,16 do m:cc(123,0,ch) end end
end
