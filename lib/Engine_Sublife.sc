// Engine_Sublife
// A bass synthesizer with articulation-aware voice design
// Designed for rich, evolving bass lines
// Sub + Saw + Pulse through Moog filter with drive and per-note envelopes

Engine_Sublife : CroneEngine {
  var <synth;
  var <bus;
  var <fxSynth;
  var <globalCutoff = 800;
  var <globalRes = 0.3;
  var <globalDrive = 0.3;
  var <globalSubMix = 0.7;
  var <globalSawMix = 0.6;
  var <globalPulseMix = 0.0;
  var <globalPulseWidth = 0.5;
  var <globalSlideTime = 0.05;
  var <globalAmpAtk = 0.01;
  var <globalAmpDec = 0.2;
  var <globalAmpSus = 0.7;
  var <globalAmpRel = 0.25;
  var <globalFiltAtk = 0.005;
  var <globalFiltDec = 0.3;
  var <globalFiltEnvAmt = 3000;
  var <globalFiltSus = 0.1;
  var <globalCompThresh = 0.6;
  var <globalCompRatio = 3.0;

  *new { arg context, doneCallback;
    ^super.new(context, doneCallback);
  }

  alloc {
    bus = Bus.audio(context.server, 2);

    // ---- BASS VOICE ----
    SynthDef(\sublife_voice, {
      arg out, freq = 110, amp = 0.5, gate = 1,
          cutoff = 800, res = 0.3, drive = 0.3,
          sub_mix = 0.7, saw_mix = 0.6, pulse_mix = 0.0, pulse_width = 0.5,
          slide_time = 0.05,
          amp_atk = 0.01, amp_dec = 0.2, amp_sus = 0.7, amp_rel = 0.25,
          filt_atk = 0.005, filt_dec = 0.3, filt_env_amt = 3000, filt_sus = 0.1,
          artic = 1, vel = 1.0;
          // artic: 1=pluck, 2=slap, 3=mute, 4=slide, 5=ghost

      var sig, sub, saw, pulse, env, filt_env, filt_freq;
      var slap_click, mute_env_mod;
      var actual_atk, actual_dec, actual_sus, actual_rel;
      var actual_filt_dec, actual_filt_amt;
      var actual_slide;

      // -- Articulation shapes the envelope --

      // Pluck: standard
      // Slap: instant attack, added click transient, bright filter burst
      // Mute: very short decay, no sustain
      // Slide: long portamento
      // Ghost: quiet, soft attack, dark filter

      actual_atk = Select.kr(artic - 1, [
        amp_atk,          // pluck
        0.001,            // slap (instant)
        0.002,            // mute (fast)
        amp_atk,          // slide
        0.03              // ghost (soft)
      ]);

      actual_dec = Select.kr(artic - 1, [
        amp_dec,          // pluck
        amp_dec * 0.7,    // slap
        0.06,             // mute (very short)
        amp_dec,          // slide
        amp_dec * 0.5     // ghost
      ]);

      actual_sus = Select.kr(artic - 1, [
        amp_sus,          // pluck
        amp_sus * 0.8,    // slap
        0.0,              // mute (no sustain!)
        amp_sus,          // slide
        amp_sus * 0.3     // ghost
      ]);

      actual_rel = Select.kr(artic - 1, [
        amp_rel,          // pluck
        amp_rel * 0.6,    // slap
        0.03,             // mute (snap off)
        amp_rel * 1.5,    // slide (longer tail)
        amp_rel * 0.4     // ghost
      ]);

      actual_filt_dec = Select.kr(artic - 1, [
        filt_dec,             // pluck
        filt_dec * 0.4,       // slap (fast bright burst)
        filt_dec * 0.1,       // mute (barely opens)
        filt_dec * 1.5,       // slide (slow sweep)
        filt_dec * 0.3        // ghost (quick dark)
      ]);

      actual_filt_amt = Select.kr(artic - 1, [
        filt_env_amt,             // pluck
        filt_env_amt * 2.5,       // slap (BRIGHT burst)
        filt_env_amt * 0.3,       // mute (dark)
        filt_env_amt * 0.8,       // slide
        filt_env_amt * 0.15       // ghost (very dark)
      ]);

      actual_slide = Select.kr(artic - 1, [
        slide_time * 0.1,     // pluck (nearly instant)
        0.001,                // slap (instant)
        0.001,                // mute (instant)
        slide_time,           // slide (full portamento!)
        slide_time * 0.3      // ghost
      ]);

      // -- Frequency with articulation-dependent portamento --
      freq = Lag.kr(freq, actual_slide);

      // -- Oscillators --
      sub = SinOsc.ar(freq) + SinOsc.ar(freq * 0.5, 0, 0.3);
      saw = VarSaw.ar(freq, 0, SinOsc.kr(0.07).range(0.3, 0.7))
            + Saw.ar(freq * 1.004, 0.3); // slight detune for thickness
      pulse = Pulse.ar(freq, pulse_width + SinOsc.kr(0.13, 0, 0.05));

      sig = (sub * sub_mix) + (saw * saw_mix) + (pulse * pulse_mix);

      // -- Slap transient (only for artic=2) --
      slap_click = EnvGen.ar(Env.perc(0.0005, 0.015)) *
                   HPF.ar(WhiteNoise.ar(0.6), 2000) *
                   (artic - 1.5).clip(0, 1); // fades in from artic 1.5+, full at 2+
      sig = sig + slap_click;

      // -- Amp envelope --
      env = EnvGen.kr(
        Env.adsr(actual_atk, actual_dec, actual_sus, actual_rel),
        gate,
        doneAction: Done.freeSelf
      );

      // -- Filter envelope --
      filt_env = EnvGen.kr(
        Env.adsr(filt_atk, actual_filt_dec, filt_sus, actual_rel),
        gate
      );
      filt_freq = cutoff + (filt_env * actual_filt_amt);
      filt_freq = filt_freq.clip(30, 16000);

      // -- Moog-style filter --
      sig = MoogFF.ar(sig, filt_freq, res * 4);

      // -- Drive / saturation --
      sig = (sig * (1 + (drive * 8))).tanh;
      sig = sig * (1 / (1 + (drive * 0.5))); // compensate gain

      // -- Final amp --
      sig = sig * env * amp * vel;

      // -- Output --
      Out.ar(out, Pan2.ar(sig, 0));
    }).add;

    // ---- MASTER FX (compression + saturation) ----
    SynthDef(\sublife_fx, {
      arg in_bus, out = 0, comp_thresh = 0.6, comp_ratio = 3.0;
      var sig;
      sig = In.ar(in_bus, 2);
      sig = Compander.ar(sig, sig,
        thresh: comp_thresh,
        slopeBelow: 1,
        slopeAbove: 1 / comp_ratio,
        clampTime: 0.005,
        relaxTime: 0.1
      );
      sig = LeakDC.ar(sig);
      Out.ar(out, sig);
    }).add;

    context.server.sync;

    // start fx bus
    fxSynth = Synth(\sublife_fx, [
      \in_bus, bus,
      \out, context.out_b,
      \comp_thresh, globalCompThresh,
      \comp_ratio, globalCompRatio
    ], context.xg);

    // ---- COMMANDS ----

    // Trigger a note with full articulation control
    this.addCommand("note_on", "fffff", { arg msg;
      // freq, vel(0-1), cutoff, artic(1-5), slide_time
      var s = Synth(\sublife_voice, [
        \out, bus,
        \freq, msg[1],
        \vel, msg[2],
        \cutoff, msg[3].max(30).min(16000),
        \artic, msg[4].round.max(1).min(5),
        \slide_time, msg[5],
        \amp, 0.7,
        \gate, 1,
        \res, globalRes,
        \drive, globalDrive,
        \sub_mix, globalSubMix,
        \saw_mix, globalSawMix,
        \pulse_mix, globalPulseMix,
        \pulse_width, globalPulseWidth,
        \amp_atk, globalAmpAtk,
        \amp_dec, globalAmpDec,
        \amp_sus, globalAmpSus,
        \amp_rel, globalAmpRel,
        \filt_atk, globalFiltAtk,
        \filt_dec, globalFiltDec,
        \filt_env_amt, globalFiltEnvAmt,
        \filt_sus, globalFiltSus,
      ], context.xg);
      // auto gate off after short time (sequencer sends gate separately)
      synth = s;
    });

    // Release current note
    this.addCommand("note_off", "", { arg msg;
      if(synth.notNil, { synth.set(\gate, 0); });
    });

    // Global filter cutoff (for arc sweeps)
    this.addCommand("cutoff", "f", { arg msg;
      globalCutoff = msg[1];
    });

    this.addCommand("resonance", "f", { arg msg;
      globalRes = msg[1];
    });

    this.addCommand("drive", "f", { arg msg;
      globalDrive = msg[1];
    });

    this.addCommand("sub_mix", "f", { arg msg;
      globalSubMix = msg[1];
    });

    this.addCommand("saw_mix", "f", { arg msg;
      globalSawMix = msg[1];
    });

    this.addCommand("pulse_mix", "f", { arg msg;
      globalPulseMix = msg[1];
    });

    this.addCommand("pulse_width", "f", { arg msg;
      globalPulseWidth = msg[1];
    });

    this.addCommand("amp_atk", "f", { arg msg;
      globalAmpAtk = msg[1];
    });

    this.addCommand("amp_dec", "f", { arg msg;
      globalAmpDec = msg[1];
    });

    this.addCommand("amp_sus", "f", { arg msg;
      globalAmpSus = msg[1];
    });

    this.addCommand("amp_rel", "f", { arg msg;
      globalAmpRel = msg[1];
    });

    this.addCommand("filt_atk", "f", { arg msg;
      globalFiltAtk = msg[1];
    });

    this.addCommand("filt_dec", "f", { arg msg;
      globalFiltDec = msg[1];
    });

    this.addCommand("filt_env_amt", "f", { arg msg;
      globalFiltEnvAmt = msg[1];
    });

    this.addCommand("filt_sus", "f", { arg msg;
      globalFiltSus = msg[1];
    });

    this.addCommand("slide_time", "f", { arg msg;
      globalSlideTime = msg[1];
    });

    this.addCommand("comp_thresh", "f", { arg msg;
      globalCompThresh = msg[1];
      fxSynth.set(\comp_thresh, msg[1]);
    });

    this.addCommand("comp_ratio", "f", { arg msg;
      globalCompRatio = msg[1];
      fxSynth.set(\comp_ratio, msg[1]);
    });
  }

  free {
    bus.free;
    fxSynth.free;
  }
}
