# DTPKDump
Script for interacting with and editing Sega DTPK files

This project started off as an attempt to extract and work with Sega AM2 DTPK audio files.  I found several existing tools, notably from KingShriek and the Shenmue team (notably Sappharad and LemonHaze), that offered a subset of the functionality I was looking for.  Notably those projects were focused primarily on playback and to a limited extent extraction.  The DTPKDump project improves upon those and expands upon those.  With it you are able to make functional modifications to DTPK files that will play back on Dreamcast hardware, as well as extracting out the audio samples contained within.  As an example of usage, I was able to modify the "Welcome to Marvel vs Capcom 2" audio cue from that game to instead play back an injected intro of my own choosing.  Usage should be fairly straight-forward, but may be a little tight just due to the limitations of scripting.  Feel free to expand and improve upon this project.  My understanding of the file format is certainly not complete, but hopefully this makes the next person's life that much easier, much as KingShriek and the Shenmue team have made my life easier.  A special thanks to Vincent for his insight and guidance on various wrinkles.  Note that DTPK is very constrained by the Yamaha AICA hardware: the 2MB limit for audio data is easy to run into.

A notable side-inclusion in this project is an updated version of KingShriek's classic dsfdtpk.py.  As I delved into the DTPK file structure, it became evident that that classic script had a simple bug wherein it presumed program group 0 was the only relevant group: but we know now that that is not the case.  I folded back in dtpkdump logic back into that tool.  It is rare that group 1+-only tracks exist, but it does happen in various instances.

DTPKDump is a command-line Python 3.x script.  The options are fairly robust:
          -showinfo         display detailed information about all DTPK contents
          -extractall       extract out all samples
          -wavconv          extract out all samples as PCM WAV files
                            (This options uses Sappharad's ADPCM to PCM conversion code.)
          -spliceadpcm (NUM) (FREQUENCY) (FILENAME)  replace sample NUM in the DTPK with the specified ADPCM file
                            Requires -out
          -spliceaiff (NUM) (FILENAME)  replace sample NUM in the DTPK with the specified AIFF file
                            AIFF files must be uncompressed 8bit or 16bit
                            Requires -out
          -splicepcm (NUM) (FILENAME)  replace sample NUM in the DTPK with the specified PCM WAV file
                            WAV files must be PCM 8bit or 16bit
                            Requires -out
          -addtrack (GROUP) (SPD) add a new track to GROUP using SPD
                            The GROUP value can be either absolute index or group descriptor (ex: a920)
                            Use special SPD value "0xbad" if you want to inject a NULL/empty track
                            Requires -out
          -addplayback (NUM) (FREQUENCY) add a new SPD using sample NUM played back at FREQUENCY
                            Requires -out
          -out (FILENAME)   save the updated DTPK file as FILENAME
                            Requires one of the splicing options.
          -options          shows the expanded list of options
          -showheaderinfo   display detailed information about the header
          -showcombinationinfo  display detailed information about the combination data
          -showprogramdefsinfo  display basic information about the program definitions data
          -showunknowninfo  display basic information about the unknown table
          -showtrackinfo    display information about the track data
          -showfulltrackinfo display detailed information about the track data
          -showplaybackinfo display detailed information about the sample playback data
                            Note that we do not show stock settings by default: use -v if you want those too
          -showeffectsinfo  display detailed information about the sample effects data
          -showsampleinfo   display detailed information about the samples
          -v                if showing Playback data show all data even if using stock values
          -dumpadpcm        extract out all ADPCM samples to raw Yamaha ADPCM files (usable in Awave Studio)
          -dumpaiff         extract out all PCM samples to PCM AIFF files (may not work for strange playback rates)
          -dumpaiffall      extract out *all* samples to PCM AIFF files (may not work for strange playback rates)
          -dumppcm          extract out all PCM samples to PCM WAV files (may not work for strange playback rates)
          -dumppcmall       extract out *all* samples to PCM WAV files (may not work for strange playback rates)
          -reassemble       rebuild the file (to test reassembly logic)
                            Requires -out
							
The most notable omission from these options is encoding incoming audio to YADPCM: I didn't find that interesting and as such have not added that support.  The playback sample frequency math is also definitely hand-wavey: it's functional enough for my needs at this time. 

At this point I believe I am mostly done with this project.  I'm able to interact meaningfully with the DTPK game aspects I care about.  If there's something this should be doing but does not, I can look into it if you give me solid information on it. 
