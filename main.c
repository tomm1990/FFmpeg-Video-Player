// tutorial07.c
// A pedagogical video player that really works! Now with seeking features.
//
// This tutorial was written by Stephen Dranger (dranger@gmail.com).
//
// Code based on FFplay, Copyright (c) 2003 Fabrice Bellard,
// and a tutorial by Martin Bohme (boehme@inb.uni-luebeckREMOVETHIS.de)
// Tested on Gentoo, CVS version 5/01/07 compiled with GCC 4.1.1
//
// Use the Makefile to build all the samples.
//
// Run using
// tutorial07 myvideofile.mpg
//
// to play the video.

#include <libavcodec/avcodec.h>
#include <libavformat/avformat.h>
#include <libavformat/avio.h>
#include <libswscale/swscale.h>
#include <libavutil/avstring.h>
#include <libavutil/time.h>

#include <SDL.h>
#include <SDL_thread.h>
#ifdef __MINGW32__
#undef  /* Prevents  from overriding () */
#endif
#include <stdio.h>
#include <math.h>

#define SDL_AUDIO_BUFFER_SIZE 1024
#define MAX_AUDIO_FRAME_SIZE 192000
#define MAX_AUDIOQ_SIZE (5 * 16 * 1024)
#define MAX_VIDEOQ_SIZE (5 * 256 * 1024)
#define AV_SYNC_THRESHOLD 0.01
#define AV_NOSYNC_THRESHOLD 10.0
#define SAMPLE_CORRECTION_PERCENT_MAX 10
#define AUDIO_DIFF_AVG_NB 20
#define FF_ALLOC_EVENT   (SDL_USEREVENT)
#define FF_REFRESH_EVENT (SDL_USEREVENT + 1)
#define FF_QUIT_EVENT (SDL_USEREVENT + 2)
#define VIDEO_PICTURE_QUEUE_SIZE 1
#define DEFAULT_AV_SYNC_TYPE AV_SYNC_VIDEO_MASTER


static int whith_colors;
static int screen_size=0;
static int screen_size_secondary=0;
static int mute=0;
static int pause=0;
static int frameCounter=0;
static int audio=0;
static int video=0;
static Uint32 normal_rhythm = 40;
static Uint32 fast_rhythm = (33/10)*10;
static Uint32 slow_rhythm = (53/10)*10;  // warning
static Uint32 rhythm = 40 ;
static int flag = 1;
static int num_of_videos_input = 0 ;
static int num_of_playing_videos = 0 ;
static int currently_playing_audio = 1;
static int status=0;
static int rhythm_number = 1000 + 0.5;
SDL_Surface *screen;

typedef struct PacketQueue{
    AVPacketList *first_pkt, *last_pkt;
    int nb_packets;
    int size;
    SDL_mutex *mutex;
    SDL_cond *cond;
} PacketQueue;

typedef struct VideoPicture {
    SDL_Overlay *bmp;
    int width, height;
    int allocated;
    double pts;
} VideoPicture;

typedef struct VideoState{
    AVFormatContext *pFormatCtx;
    int             quit, pictq_size, pictq_rindex, pictq_windex, audio_diff_avg_count, audio_hw_buf_size, audio_pkt_size, seek_flags, seek_req, i, videoStream, audioStream , video_id , av_sync_type;
    double          external_clock; /* external clock base */
    int64_t         video_current_pts_time, seek_pos, external_clock_time;
    double          audio_clock;
    AVStream        *audio_st , *video_st;
    PacketQueue     videoq, audioq;
    AVFrame         audio_frame;
    uint8_t         audio_buf[(MAX_AUDIO_FRAME_SIZE * 3) / 2];
    unsigned int    audio_buf_size , audio_buf_index;
    AVPacket        audio_pkt;
    uint8_t         *audio_pkt_data;
    double          audio_diff_cum, video_current_pts, video_clock, frame_last_delay, frame_last_pts, frame_timer, audio_diff_threshold, audio_diff_avg_coef;
    VideoPicture    pictq[VIDEO_PICTURE_QUEUE_SIZE];
    SDL_mutex       *pictq_mutex;
    SDL_cond        *pictq_cond;
    SDL_Thread      *video_tid, *parse_tid;
    char            filename[1024];
    AVIOContext     *io_context;
    struct SwsContext *sws_ctx;
} VideoState;

VideoState clips[2];

enum {
    AV_SYNC_AUDIO_MASTER,
    AV_SYNC_VIDEO_MASTER,
    AV_SYNC_EXTERNAL_MASTER,
};

/* Since we only have one decoding thread, the Big Struct
   can be global in case we need it. */
VideoState *global_video_state;
AVPacket flush_pkt;

void packet_queue_init(PacketQueue *q) {
    memset(q, 0, sizeof(PacketQueue));
    q->mutex = SDL_CreateMutex();
    q->cond = SDL_CreateCond();
}

int packet_queue_put(PacketQueue *q, AVPacket *pkt) {
    AVPacketList *pkt1;
    if(pkt != &flush_pkt && av_dup_packet(pkt) < 0) return -1;
    pkt1 = av_malloc(sizeof(AVPacketList));
    if (!pkt1) return -1;
    pkt1->pkt = *pkt;
    pkt1->next = NULL;
    SDL_LockMutex(q->mutex);
    if (!q->last_pkt) q->first_pkt = pkt1;
    else q->last_pkt->next = pkt1;
    q->last_pkt = pkt1;
    q->nb_packets++;
    q->size += pkt1->pkt.size;
    SDL_CondSignal(q->cond);
    SDL_UnlockMutex(q->mutex);
    return 0;
}

static int packet_queue_get(PacketQueue *q, AVPacket *pkt, int block){
    AVPacketList *pkt1;
    int ret;
    SDL_LockMutex(q->mutex);
    for(;;) {
        if(global_video_state->quit) {
            ret = -1;
            break;
        }
        pkt1 = q->first_pkt;
        if (pkt1) {
            q->first_pkt = pkt1->next;
            if (!q->first_pkt) q->last_pkt = NULL;
            q->nb_packets--;
            q->size -= pkt1->pkt.size;
            *pkt = pkt1->pkt;
            av_free(pkt1);
            ret = 1;
            break;
        } else if (!block) {
            ret = 0;
            break;
        } else {
            SDL_CondWait(q->cond, q->mutex);
        }
    }
    SDL_UnlockMutex(q->mutex);
    return ret;
}

static void packet_queue_flush(PacketQueue *q) {
    AVPacketList *pkt, *pkt1;
    SDL_LockMutex(q->mutex);
    for(pkt = q->first_pkt; pkt != NULL; pkt = pkt1) {
        pkt1 = pkt->next;
        av_free_packet(&pkt->pkt);
        av_freep(&pkt);
    }
    q->last_pkt = NULL;
    q->first_pkt = NULL;
    q->nb_packets = 0;
    q->size = 0;
    SDL_UnlockMutex(q->mutex);
}

double get_audio_clock(VideoState *is) {
    double pts;
    int hw_buf_size, bytes_per_sec, n;
    pts = is->audio_clock;
    hw_buf_size = is->audio_buf_size - is->audio_buf_index;
    bytes_per_sec = 0;
    n = is->audio_st->codec->channels * 2;
    if(is->audio_st) bytes_per_sec = is->audio_st->codec->sample_rate * n;
    if(bytes_per_sec) pts -= (double)hw_buf_size / bytes_per_sec;
    return pts;
}

double get_video_clock(VideoState *is) {
    return is->video_current_pts + (av_gettime() - is->video_current_pts_time) / 1000000.0;
}

double get_external_clock(VideoState *is) {
    return av_gettime() / 1000000.0;
}

double get_master_clock(VideoState *is) {
    if(is->av_sync_type == AV_SYNC_VIDEO_MASTER) return get_video_clock(is);
    else if(is->av_sync_type == AV_SYNC_AUDIO_MASTER) return get_audio_clock(is);
    else return get_external_clock(is);
}

/* Add or subtract samples to get a better sync, return new
   audio buffer size */
int synchronize_audio(VideoState *is, short *samples, int samples_size, double pts) {
    int n = 2 * is->audio_st->codec->channels;
    double ref_clock;
    if(is->av_sync_type != AV_SYNC_AUDIO_MASTER) {
        double diff, avg_diff;
        int wanted_size, min_size, max_size /*, nb_samples */;
        ref_clock = get_master_clock(is);
        diff = get_audio_clock(is) - ref_clock;
        if(diff < AV_NOSYNC_THRESHOLD) {
            // accumulate the diffs
            is->audio_diff_cum = diff + is->audio_diff_avg_coef
            *is->audio_diff_cum;
            if(is->audio_diff_avg_count < AUDIO_DIFF_AVG_NB) is->audio_diff_avg_count++;
            else {
                avg_diff = is->audio_diff_cum * (1.0 - is->audio_diff_avg_coef);
                if(fabs(avg_diff) >= is->audio_diff_threshold) {
                    wanted_size = samples_size + ((int)(diff * is->audio_st->codec->sample_rate) * n);
                    min_size = samples_size * ((100 - SAMPLE_CORRECTION_PERCENT_MAX) / 100);
                    max_size = samples_size * ((100 + SAMPLE_CORRECTION_PERCENT_MAX) / 100);
                    if(wanted_size < min_size) wanted_size = min_size;
                    else if (wanted_size > max_size) wanted_size = max_size;
                    if(wanted_size < samples_size) samples_size = wanted_size;
                    else if(wanted_size > samples_size) {
                        uint8_t *samples_end, *q;
                        int nb = (samples_size - wanted_size);
                        samples_end = (uint8_t *)samples + samples_size - n;
                        q = samples_end + n;
                        while(nb > 0) {
                            memcpy(q, samples_end, n);
                            q += n;
                            nb -= n;
                        }
                        samples_size = wanted_size;
                    }
                }
            }
        } else {
            /* difference is TOO big; reset diff stuff */
            is->audio_diff_avg_count = is->audio_diff_cum =  0;
        }
    }
    return samples_size;
}

int audio_decode_frame(VideoState *is, double *pts_ptr) {
    int len1, data_size = 0, n;
    AVPacket *pkt = &is->audio_pkt;
    double pts;
    for(;;) {
        while(is->audio_pkt_size > 0) {
            int got_frame = 0;
            len1 = avcodec_decode_audio4(is->audio_st->codec, &is->audio_frame, &got_frame, pkt);
            if(len1 < 0) {  is->audio_pkt_size = 0;  break;  }
            if (got_frame){
                data_size = av_samples_get_buffer_size(
                    NULL,
                    is->audio_st->codec->channels,
                    is->audio_frame.nb_samples,
                    is->audio_st->codec->sample_fmt,
                    1 );
                memcpy(is->audio_buf, is->audio_frame.data[0], data_size);
            }
            is->audio_pkt_data += len1;
            is->audio_pkt_size -= len1;
            if(data_size <= 0) continue;
            pts = is->audio_clock;
            *pts_ptr = pts;
            n = 2 * is->audio_st->codec->channels;
            is->audio_clock += (double)data_size/(double)(n * is->audio_st->codec->sample_rate);
            /* We have data, return it and come back for more later */
            return data_size;
        }
        if(pkt->data) av_free_packet(pkt);
        if(is->quit) return -1;
        /* next packet */
        if(packet_queue_get(&is->audioq, pkt, 1) < 0) return -1;
        if(pkt->data == flush_pkt.data) { avcodec_flush_buffers(is->audio_st->codec); continue; }
        is->audio_pkt_data = pkt->data;
        is->audio_pkt_size = pkt->size;
        /* if update, update the audio clock w/pts */
        if(pkt->pts != AV_NOPTS_VALUE) is->audio_clock = av_q2d(is->audio_st->time_base)*pkt->pts;

    }
}

void audio_callback(void *userdata, Uint8 *stream, int len) {
    VideoState *is = &clips[audio];
    int len1, audio_size;
    double pts;
    while(len > 0) {
        if(is->audio_buf_index >= is->audio_buf_size) {
            /* We have already sent all our data; get more */
            audio_size = audio_decode_frame(is, &pts);
            if(audio_size < 0) {
                /* If error, output silence */
                is->audio_buf_size = 1024;
                memset(is->audio_buf, 0, is->audio_buf_size);
            } else {
                audio_size = synchronize_audio(is, (int16_t *)is->audio_buf, audio_size, pts);
                is->audio_buf_size = audio_size;
            }
            is->audio_buf_index = 0;
        }
        len1 = is->audio_buf_size - is->audio_buf_index;
        if(len1 > len) len1 = len;
        if(mute==0) memcpy(stream, (uint8_t *)is->audio_buf + is->audio_buf_index, len1);
        len -= len1;
        stream += len1;
        is->audio_buf_index += len1;
    }
}

static Uint32 sdl_refresh_timer_cb(Uint32 interval, void *opaque) {
    SDL_Event event;
    event.type = FF_REFRESH_EVENT;
    event.user.data1 = opaque;
    SDL_PushEvent(&event);
    return 0; /* 0 means stop timer */
}

/* schedule a video refresh in 'delay' ms */
static void schedule_refresh(VideoState *is, Uint32 delay) {
    SDL_AddTimer(  delay , sdl_refresh_timer_cb, is);
}

AVFrame* convertToRGB(AVFrame* pFrame, VideoState* is){
    AVFrame *pFrameRGB = NULL;
    uint8_t *buffer = NULL;
    int numBytes;
    struct SwsContext *sws_ctx = NULL;

    // Allocate an AVFrame structure
    pFrameRGB=av_frame_alloc();
    if(pFrameRGB==NULL) return NULL;

    // Determine required buffer size and allocate buffer
    numBytes=avpicture_get_size(PIX_FMT_RGB24, is->video_st->codec->width, is->video_st->codec->height);
    buffer=(uint8_t *)av_malloc(numBytes*sizeof(uint8_t));

    // Assign appropriate parts of buffer to image planes in pFrameRGB
    // Note that pFrameRGB is an AVFrame, but AVFrame is a superset
    // of AVPicture
    avpicture_fill((AVPicture *)pFrameRGB, buffer, PIX_FMT_RGB24, is->video_st->codec->width, is->video_st->codec->height);

    // initialize SWS context for software scaling
    sws_ctx = sws_getContext(is->video_st->codec->width,
			   is->video_st->codec->height,
			   is->video_st->codec->pix_fmt,
			   is->video_st->codec->width,
			   is->video_st->codec->height,
			   PIX_FMT_RGB24,
			   SWS_BILINEAR,
			   NULL,
			   NULL,
			   NULL
			   );

	// Convert the image from its native format to RGB
	sws_scale(sws_ctx, (uint8_t const * const *)pFrame->data,
		  pFrame->linesize, 0, is->video_st->codec->height,
		  pFrameRGB->data, pFrameRGB->linesize);

    return pFrameRGB;
}

void video_display(VideoState *is) {
    SDL_Rect rect;
    VideoPicture *vp;
    float aspect_ratio;
    int w, h, x, y;
    vp = &is->pictq[is->pictq_rindex];
    if(vp->bmp) {
        if(is->video_st->codec->sample_aspect_ratio.num == 0) aspect_ratio = 0;
        else {
            aspect_ratio = av_q2d(is->video_st->codec->sample_aspect_ratio) *
                is->video_st->codec->width / is->video_st->codec->height;
        }
        if(aspect_ratio <= 0.0) aspect_ratio = (float)is->video_st->codec->width / (float)is->video_st->codec->height;
        h = screen->h;
        w = ((int)rint(h * aspect_ratio)) ;
        if(w > screen->w) {
            w = screen->w;
            h = ((int)rint(w / aspect_ratio)) ;
        }
        rect.x = (screen->w - w) / 2;
        rect.y = (screen->h - h) / 2;
        if(status==0){
            if(  is->video_id == 0 ){
                rect.w = w;
                rect.h = h;
                SDL_DisplayYUVOverlay(vp->bmp, &rect);
            }
            else if( is->video_id == 1 ){
                rect.w = w/2;
                rect.h = h/2;
                SDL_DisplayYUVOverlay(vp->bmp, &rect);
            }
        } else if(status==1){
            if(  is->video_id == video ){
                rect.w = w;
                rect.h = h;
                SDL_DisplayYUVOverlay(vp->bmp, &rect);
            }
        }
    }
}

void video_refresh_timer(void *userdata) {
    VideoState *is = (VideoState *)userdata;
    VideoPicture *vp;
    double actual_delay, delay, sync_threshold, ref_clock, diff;
    if(is->video_st) {
        if(is->pictq_size == 0) {
        schedule_refresh(is, 100);
    } else {
        vp = &is->pictq[is->pictq_rindex];
        is->video_current_pts = vp->pts;
        is->video_current_pts_time = av_gettime();
        delay = vp->pts - is->frame_last_pts; /* the pts from last time */
        if(delay <= 0 || delay >= 1.0) delay = is->frame_last_delay;

        /* save for next time */
        is->frame_last_delay = delay;
        is->frame_last_pts = vp->pts;

        /* update delay to sync to audio if not master source */
        if(is->av_sync_type != AV_SYNC_VIDEO_MASTER) {
            ref_clock = get_master_clock(is);
            diff = vp->pts - ref_clock;

            /* Skip or repeat the frame. Take delay into account
            FFPlay still doesn't "know if this is the best guess." */
            sync_threshold = (delay > AV_SYNC_THRESHOLD) ? delay : AV_SYNC_THRESHOLD;
            if(fabs(diff) < AV_NOSYNC_THRESHOLD) {
                if(diff <= -sync_threshold) delay = 0;
                else if(diff >= sync_threshold) delay = 2 * delay;
            }
        }
        is->frame_timer += delay;

        /* computer the REAL delay */
        actual_delay = ((is->frame_timer - (av_gettime() / 1000000.0)));
        if(actual_delay < 0.010) actual_delay = 0.010;
        schedule_refresh(is, (Uint32)(actual_delay * rhythm_number ));

        /* show the picture! */
        video_display(is);

        /* update queue for next picture! */
        if(++is->pictq_rindex == VIDEO_PICTURE_QUEUE_SIZE) 	is->pictq_rindex = 0;
        SDL_LockMutex(is->pictq_mutex);
        is->pictq_size--;
        SDL_CondSignal(is->pictq_cond);
        SDL_UnlockMutex(is->pictq_mutex);
    }
  } else schedule_refresh(is, 100);
}

void alloc_picture(void *userdata) {
    VideoState *is = (VideoState *)userdata;
    VideoPicture *vp;
    vp = &is->pictq[is->pictq_windex];
    if(vp->bmp) SDL_FreeYUVOverlay(vp->bmp);

  // Allocate a place to put our YUV image on that screen
    vp->bmp = SDL_CreateYUVOverlay(is->video_st->codec->width,
				 is->video_st->codec->height,
				 SDL_YV12_OVERLAY,
				 screen);
    vp->width = is->video_st->codec->width;
    vp->height = is->video_st->codec->height;
    SDL_LockMutex(is->pictq_mutex);
    vp->allocated = 1;
    SDL_CondSignal(is->pictq_cond);
    SDL_UnlockMutex(is->pictq_mutex);
}

int queue_picture(VideoState *is, AVFrame *pFrame, double pts) {
    VideoPicture *vp;
    AVPicture pict;

    /* wait until we have space for a new pic */
    SDL_LockMutex(is->pictq_mutex);
    while(is->pictq_size >= VIDEO_PICTURE_QUEUE_SIZE && !is->quit) SDL_CondWait(is->pictq_cond, is->pictq_mutex);
    SDL_UnlockMutex(is->pictq_mutex);
    if(is->quit) return -1;

    // windex is set to 0 initially
    vp = &is->pictq[is->pictq_windex];

    /* allocate or resize the buffer! */
    if(!vp->bmp ||
     vp->width != is->video_st->codec->width ||
     vp->height != is->video_st->codec->height) {
        SDL_Event event;
        vp->allocated = 0;
        /* we have to do it in the  thread */
        event.type = FF_ALLOC_EVENT;
        event.user.data1 = is;
        SDL_PushEvent(&event);

        /* wait until we have a picture allocated */
        SDL_LockMutex(is->pictq_mutex);
        while(!vp->allocated && !is->quit) SDL_CondWait(is->pictq_cond, is->pictq_mutex);
        SDL_UnlockMutex(is->pictq_mutex);
        if(is->quit) return -1;
  }
  /* We have a place to put our picture on the queue */
  /* If we are skipping a frame, do we set this to null
     but still return vp->allocated = 1? */


  if(vp->bmp) {

    SDL_LockYUVOverlay(vp->bmp);

    //dst_pix_fmt = PIX_FMT_YUV420P;
    /* point pict at the queue */

    pict.data[0] = vp->bmp->pixels[0];
    pict.data[1] = vp->bmp->pixels[2];
    pict.data[2] = vp->bmp->pixels[1];

    pict.linesize[0] = vp->bmp->pitches[0];
    pict.linesize[1] = vp->bmp->pitches[2];
    pict.linesize[2] = vp->bmp->pitches[1];

    // Convert the image into YUV format that  uses

    sws_scale
    (
        is->sws_ctx,
        (uint8_t const * const *)pFrame->data,
        pFrame->linesize,
        0,
        is->video_st->codec->height,
        pict.data,
        pict.linesize
    );

    SDL_UnlockYUVOverlay(vp->bmp);
    vp->pts = pts;

    /* now we inform our display thread that we have a pic ready */
    if(++is->pictq_windex == VIDEO_PICTURE_QUEUE_SIZE) {
      is->pictq_windex = 0;
    }
    SDL_LockMutex(is->pictq_mutex);
    is->pictq_size++;
    SDL_UnlockMutex(is->pictq_mutex);
  }
  return 0;
}

double synchronize_video(VideoState *is, AVFrame *src_frame, double pts) {
    double frame_delay;
    if(pts != 0) is->video_clock = pts ;
    else pts = is->video_clock;

    /* update the video clock */
    frame_delay = av_q2d(is->video_st->codec->time_base);

    /* if we are repeating a frame, adjust clock accordingly */
    frame_delay += src_frame->repeat_pict * (frame_delay * 0.5);
    is->video_clock += frame_delay;
    return pts;
}

uint64_t global_video_pkt_pts = AV_NOPTS_VALUE;

/* These are called whenever we allocate a frame
 * buffer. We use this to store the global_pts in
 * a frame at the time it is allocated.
 */
int our_get_buffer(struct AVCodecContext *c, AVFrame *pic) {
    int ret = avcodec_default_get_buffer(c, pic);
    uint64_t *pts = av_malloc(sizeof(uint64_t));
    *pts = global_video_pkt_pts;
    pic->opaque = pts;
    return ret;
}

void our_release_buffer(struct AVCodecContext *c, AVFrame *pic) {
    if(pic) av_freep(&pic->opaque);
    avcodec_default_release_buffer(c, pic);
}

int video_thread(void *arg) {
    AVFormatContext *pFormatCtx = NULL;
    VideoState *is = (VideoState *)arg;
    AVPacket pkt1, *packet = &pkt1;
    int numBytes, i, frameFinished;
    AVCodecContext  *pCodecCtx = NULL;
    AVCodec         *pCodec = NULL;
    AVFrame *pFrame, *pFrameRGB;
    uint8_t *buffer = NULL;
    double pts;
    struct SwsContext *sws_ctx = NULL;

    // Allocate video frame
    pFrame=av_frame_alloc();

    // Allocate an AVFrame structure
    pFrameRGB=av_frame_alloc();
    if(pFrameRGB==NULL) return -1;

    for(;;) {
        if(packet_queue_get(&is->videoq, packet, 1) < 0) break;
        if(packet->data == flush_pkt.data) {
            avcodec_flush_buffers(is->video_st->codec);
            continue;
    }
    pts = 0;

    // Save global pts to be stored in pFrame in first call
    global_video_pkt_pts = packet->pts;
    // Decode video frame
    avcodec_decode_video2(is->video_st->codec, pFrame, &frameFinished,
				packet);
    if(packet->dts == AV_NOPTS_VALUE && pFrame->opaque && *(uint64_t*)pFrame->opaque != AV_NOPTS_VALUE) {
        pts = *(uint64_t *)pFrame->opaque;
    } else if(packet->dts != AV_NOPTS_VALUE) pts = packet->dts;
    else pts = 0;
    pts *= av_q2d(is->video_st->time_base);

    // Did we get a video frame?
    if(frameFinished) {
        pts = synchronize_video(is, pFrame, pts);
        if (whith_colors==-1){
            for (int y = 0; y < pFrame->height / 2 ; y++) {
                for (int x = 0; x < pFrame->width; x++) {
                    pFrame->data[1][y * pFrame->linesize[1] + x] = 125;
                    pFrame->data[2][y * pFrame->linesize[2] + x] = 125;
                }
            }
        }
        if (whith_colors==1){   // RED
            for (int y = 0; y < pFrame->height / 2 ; y++) {
                for (int x = 0; x < pFrame->width; x++) {
                    pFrame->data[1][y * pFrame->linesize[1] + x] = 350;
                    pFrame->data[2][y * pFrame->linesize[2] + x] = 250;
                }
            }
        }
        if (whith_colors==2){   // GREEN
            for (int y = 0; y < pFrame->height / 2 ; y++) {
                for (int x = 0; x < pFrame->width; x++) {
                    pFrame->data[1][y * pFrame->linesize[1] + x] = 0;
                    pFrame->data[2][y * pFrame->linesize[2] + x] = 0;
                }
            }
        }
        if (whith_colors==3){   //  BLUE
            for (int y = 0; y < pFrame->height/2; y++) {
                for (int x = 0; x < pFrame->width; x++) {
                    pFrame->data[1][y * pFrame->linesize[1] + x] = 250;
                    pFrame->data[2][y * pFrame->linesize[2] + x] = 350;
                }
            }
        }
        if (pause==1){      // Snapshot
            AVFrame *pFrameRGB = convertToRGB(pFrame , is);
            SaveFrame(pFrameRGB,is->video_st->codec->width,is->video_st->codec->height,frameCounter);
            pause=0;
        }
        if(queue_picture(is, pFrame, pts) < 0) break;

    }
    av_free_packet(packet);
  }
  av_free(pFrame);
  return 0;
}

int stream_component_open(VideoState *is, int stream_index) {
    AVFormatContext *pFormatCtx = is->pFormatCtx;
    AVCodecContext *codecCtx = NULL;
    AVCodec *codec = NULL;
    AVDictionary *optionsDict = NULL;
    SDL_AudioSpec wanted_spec, spec;
    if(stream_index < 0 || stream_index >= pFormatCtx->nb_streams) return -1;

    // Get a pointer to the codec context for the video stream
    codecCtx = pFormatCtx->streams[stream_index]->codec;
        if (codecCtx->sample_fmt == AV_SAMPLE_FMT_S16P) codecCtx->request_sample_fmt = AV_SAMPLE_FMT_S16;
        if (codecCtx->sample_fmt == AV_SAMPLE_FMT_S16P) codecCtx->request_sample_fmt = AV_SAMPLE_FMT_S16;
        if (codecCtx->sample_fmt == AV_SAMPLE_FMT_S16P) codecCtx->request_sample_fmt = AV_SAMPLE_FMT_S16;

        if(codecCtx->codec_type == AVMEDIA_TYPE_AUDIO) {
            // Set audio settings from codec info
            wanted_spec.freq = codecCtx->sample_rate;
            wanted_spec.format = AUDIO_S16SYS;
            wanted_spec.channels = codecCtx->channels;
            wanted_spec.silence = 0;
            wanted_spec.samples = SDL_AUDIO_BUFFER_SIZE;
            wanted_spec.callback = audio_callback;
            wanted_spec.userdata = is;

            if(is->video_id==audio){
                if(SDL_OpenAudio(&wanted_spec, &spec) < 0) {
                    fprintf(stderr, "SDL_OpenAudio: %s\n", SDL_GetError());
                    return -1;
                }
            }
            is->audio_hw_buf_size = spec.size;
        }
        codec = avcodec_find_decoder(codecCtx->codec_id);
        if(!codec || (avcodec_open2(codecCtx, codec, &optionsDict) < 0)) {
            fprintf(stderr, "Unsupported codec!\n");
            return -1;
        }

        switch(codecCtx->codec_type) {
            case AVMEDIA_TYPE_AUDIO:
                is->audioStream = stream_index;
                is->audio_st = pFormatCtx->streams[stream_index];
                is->audio_buf_size = 0;
                is->audio_buf_index = 0;

                /* averaging filter for audio sync */
                is->audio_diff_avg_coef = exp(log(0.01 / AUDIO_DIFF_AVG_NB));
                is->audio_diff_avg_count = 0;
                /* Correct audio only if larger error than this */
                is->audio_diff_threshold = 2.0 * SDL_AUDIO_BUFFER_SIZE / codecCtx->sample_rate;
                memset(&is->audio_pkt, 0, sizeof(is->audio_pkt));
                packet_queue_init(&is->audioq);
                SDL_PauseAudio(0);
                break;
            case AVMEDIA_TYPE_VIDEO:
                is->videoStream = stream_index;
                is->video_st = pFormatCtx->streams[stream_index];
                is->frame_timer = (double)av_gettime() / 1000000.0;
                is->frame_last_delay = 40e-3;
                is->video_current_pts_time = av_gettime();
                packet_queue_init(&is->videoq);
                is->video_tid = SDL_CreateThread(video_thread, is);
                is->sws_ctx = sws_getContext(
                    is->video_st->codec->width,
                    is->video_st->codec->height,
                    is->video_st->codec->pix_fmt,
                    is->video_st->codec->width,
                    is->video_st->codec->height,
                    PIX_FMT_YUV420P,
                    SWS_BILINEAR,
                    NULL,
                    NULL,
                    NULL);
                codecCtx->get_buffer2 = our_get_buffer;
                codecCtx->release_buffer = our_release_buffer;
                break;
            default:
                break;
    }
    return 0;
}

int decode_interrupt_cb(void *opaque) {
  return (global_video_state && global_video_state->quit);
}

int decode_thread(void *arg) {
    VideoState *is = (VideoState*)arg;
    AVFormatContext *pFormatCtx = NULL;
    AVPacket pkt1, *packet = &pkt1;
    AVDictionary *io_dict = NULL;
    AVIOInterruptCB callback;
    int video_index = -1, audio_index = -1 ,i;
    is->videoStream=-1;
    is->audioStream=-1;
    global_video_state = is;

    // will interrupt blocking functions if we quit!
    callback.callback = decode_interrupt_cb;
    callback.opaque = is;
    if (avio_open2(&is->io_context, is->filename, 0, &callback, &io_dict)){
        fprintf(stderr, "Unable to open I/O for %s\n", is->filename);
        return -1;
    }

    // Open video file
    if(avformat_open_input(&pFormatCtx, is->filename, NULL, NULL)!=0) return -1; // Couldn't open file

    is->pFormatCtx = pFormatCtx;

    // Retrieve stream information
    if(avformat_find_stream_info(pFormatCtx, NULL)<0) return -1; // Couldn't find stream information

    // Dump information about file onto standard error
    av_dump_format(pFormatCtx, 0, is->filename, 0);

    // Find the first video stream
    for(i = 0 ; i < pFormatCtx->nb_streams; i++) {
        if(pFormatCtx->streams[i]->codec->codec_type==AVMEDIA_TYPE_VIDEO && video_index < 0) video_index=i;
        if(pFormatCtx->streams[i]->codec->codec_type==AVMEDIA_TYPE_AUDIO && audio_index < 0) audio_index=i;
    }
    if(audio_index >= 0) stream_component_open(is, audio_index);
    if(video_index >= 0)  stream_component_open(is, video_index);

    if(is->videoStream < 0 || is->audioStream < 0) {
        fprintf(stderr, "%s: could not open codecs\n", is->filename);
        goto fail;
    }

    for(;;) {
        if(is->quit) break;

        // seek stuff goes here
        if(is->seek_req) {
            printf("if(is->seek_req)\n");
            int stream_index= -1;
            int64_t seek_target = is->seek_pos;
            if     (is->videoStream >= 0) stream_index = is->videoStream;
            else if(is->audioStream >= 0) stream_index = is->audioStream;
            if(stream_index>=0) seek_target= av_rescale_q(seek_target, AV_TIME_BASE_Q, pFormatCtx->streams[stream_index]->time_base);
            if(av_seek_frame(is->pFormatCtx, stream_index, seek_target, is->seek_flags) < 0) {
                fprintf(stderr, "%s: error while seeking\n", is->pFormatCtx->filename);
            } else {
                if(is->audioStream >= 0) {
                    packet_queue_flush(&is->audioq);
                    packet_queue_put(&is->audioq, &flush_pkt);
                }
                if(is->videoStream >= 0) {
                    packet_queue_flush(&is->videoq);
                    packet_queue_put(&is->videoq, &flush_pkt);
                }
            }
            is->seek_req = 0;
        }
        if(av_read_frame(is->pFormatCtx, packet) < 0) {
            if(is->pFormatCtx->pb->error == 0) {
                SDL_Delay(10); /* no error; wait for user input */
                continue;
            } else break;
        }
        // Is this a packet from the video stream?
        if(packet->stream_index == is->videoStream) packet_queue_put(&is->videoq, packet);
        else if(packet->stream_index == is->audioStream) packet_queue_put(&is->audioq, packet);
        else av_free_packet(packet);
    }
    /* all done - wait for it */
    while(!is->quit) SDL_Delay(100);
    fail:
    {
        printf("fail\n");
        SDL_Event event;
        event.type = FF_QUIT_EVENT;
        event.user.data1 = is;
        SDL_PushEvent(&event);
    }
    return 0;
}

void stream_seek(VideoState *is, int64_t pos, int rel) {
  if(!is->seek_req) {
    is->seek_pos = pos;
    is->seek_flags = rel < 0 ? AVSEEK_FLAG_BACKWARD : 0;
    is->seek_req = 1;
  }
}

int main(int argc, char *argv[]) {
    SDL_Event event;
    int i=0;
    if(argc != 3) {
        printf("! Wrong input !\nPlease provide one or two videos names as arguments\nFollow Readme.txt file\n");
        printf("i.e -> ./video_player first.mpg second.mpg\n");
        printf("i.e -> ./video_player first.mpg 100\n");
        exit(1);
    }
    char* video_name_a = argv[1];
    printf("----------------------\nFirst Video Name : %s\n",video_name_a);
    int sizeof_video_a = atoi(argv[2]);
    char* video_name_b;
    if(sizeof_video_a){
        printf("First Video Size : %d\n----------------------\n",sizeof_video_a);
        currently_playing_audio = num_of_playing_videos = num_of_videos_input = 1;
        // one video with size
        screen_size_secondary = sizeof_video_a;
        screen = SDL_SetVideoMode(sizeof_video_a, sizeof_video_a, 24, 0);
    } else {
        video_name_b = argv[2];
        num_of_playing_videos = num_of_videos_input = 2;
        currently_playing_audio = 1;
        printf("Second Video Name : %s\n----------------------\n",video_name_b);
        // two videos
        screen = SDL_SetVideoMode(640, 480, 24, 0);
    }
    argc=argc-1;
    printf("Number of Videos: %d\n",num_of_videos_input);

    // Register all formats and codecs
    av_register_all();

    if(SDL_Init(SDL_INIT_VIDEO | SDL_INIT_AUDIO | SDL_INIT_TIMER)) {
        fprintf(stderr, "Could not initialize SDL - %s\n", SDL_GetError());
        exit(1);
    }
    if(!screen) {
        fprintf(stderr, "SDL: could not set video mode - exiting\n");
        exit(1);
    }
    if(num_of_videos_input==2){
        for(i;i < argc;++i){
            clips[i].video_id = i;

            // Copy the string src to dst, but no more than size - 1 bytes, and null-terminate dst.
            av_strlcpy(clips[i].filename, argv[i+1], 30);

            clips[i].pictq_mutex = SDL_CreateMutex();
            clips[i].pictq_cond = SDL_CreateCond();

            if (!clips[i].pictq_mutex) {
                fprintf(stderr, "Couldn't create pictq_mutex - %s\n", SDL_GetError() );
                exit(1);
            }

            if (!clips[i].pictq_cond) {
                fprintf(stderr, "Couldn't create pictq_cond - %s\n", SDL_GetError() );
                exit(1);
            }
            schedule_refresh(&clips[i], rhythm);
            clips[i].av_sync_type = AV_SYNC_VIDEO_MASTER;
            clips[i].parse_tid = SDL_CreateThread(decode_thread, &clips[i]);
            if(!clips[i].parse_tid) {
                fprintf(stderr, "Couldn't create SDL_CreateThread - %s\n", SDL_GetError() );
                av_free(&clips[i]);
                return -1;
            }
        }

    } else {
        clips[0].video_id = i;
        av_strlcpy(clips[0].filename, argv[1], 30);
        clips[0].pictq_mutex = SDL_CreateMutex();
        clips[0].pictq_cond = SDL_CreateCond();
        if (!clips[0].pictq_mutex) {
            fprintf(stderr, "Couldn't create pictq_mutex - %s\n", SDL_GetError() );
            exit(1);
        }
        if (!clips[0].pictq_cond) {
            fprintf(stderr, "Couldn't create pictq_cond - %s\n", SDL_GetError() );
            exit(1);
        }
        schedule_refresh(&clips[i], rhythm);
        clips[0].av_sync_type = AV_SYNC_VIDEO_MASTER;
        clips[0].parse_tid = SDL_CreateThread(decode_thread, &clips[0]);
        if(!clips[0].parse_tid) {
            fprintf(stderr, "Couldn't create SDL_CreateThread - %s\n", SDL_GetError() );
            av_free(&clips[0]);
            return -1;
        }
    }

    // Initialize optional fields of a packet with default values.
    av_init_packet(&flush_pkt);
    flush_pkt.data = (unsigned char *)"FLUSH";

    for(;;) {
        double incr, pos;
        SDL_WaitEvent(&event);
        switch(event.type) {
            case SDL_KEYDOWN:
                switch(event.key.keysym.sym) {
                    case SDLK_w:           // Cahnge to Black and White
                        whith_colors=-1;
                        break;

                    case SDLK_c:           // Change to Color
                        whith_colors=0;
                        break;

                    case SDLK_r:           // Change to Red view
                        whith_colors=1;
                        break;

                    case SDLK_g:           // Change to Green view
                        whith_colors=2;
                        break;

                    case SDLK_b:           // Change to Blue view
                        whith_colors=3;
                        break;

                    case SDLK_o :          // Change to one video view
                        status = 1;
                        break;

                    case SDLK_m :          // Change to multiple vidoes view
                        status = 0;
                        break;

                    case SDLK_x:          // Take a snapshot
                        ++frameCounter;
                        if(pause==0) pause=1;
                        else pause=0;
                        break;

                    case SDLK_1:           // Change to first video audio
                        audio=0;
                        break;

                    case SDLK_2:           // Change to second video audio
                        audio=1;
                        break;

                    case SDLK_f :          // Change to fast forward mode
                        rhythm_number = 0;
                        break;

                    case SDLK_s :          // Change to slow motion mode
                        rhythm = normal_rhythm / 2;
                        break;

                    case SDLK_n :          // Change to noraml rhythm mode
                        rhythm_number = 1000 + 0.5;
                        break;

                    default:
                        break;
                }
                break;
                case FF_QUIT_EVENT:
                case SDL_QUIT:
                    clips[i].quit = 0;
      /*
       * If the video has finished playing, then both the picture and
       * audio queues are waiting for more data.  Make them stop
       * waiting and terminate normally.
       */
                    exit(0);
                    break;
                case FF_ALLOC_EVENT:
                    alloc_picture(event.user.data1);
                    break;
                case FF_REFRESH_EVENT:
                    video_refresh_timer(event.user.data1);
                    break;
                default:
                    break;
            }
    }
    return 0;
}

void SaveFrame(AVFrame *pFrame, int width, int height, int iFrame) {
  FILE *pFile;
  char szFilename[32];
  int  y;
  // Open file
  sprintf(szFilename, "frame%d.ppm", iFrame);
  pFile=fopen(szFilename, "wb");
  if(pFile==NULL)
    return;

  // Write header
  fprintf(pFile, "P6\n%d %d\n255\n", width, height);


  // Write pixel data
  for(y=0; y<height; y++)
    fwrite(pFrame->data[0]+y*pFrame->linesize[0], 1, width*3, pFile);

  // Close file
  fclose(pFile);
}

int create_thread(void *arg) {
  VideoState *is = (VideoState *)arg;
  AVFormatContext *pFormatCtx = NULL;
  AVPacket pkt1, *packet = &pkt1;
  AVDictionary *io_dict = NULL;
  AVIOInterruptCB callback;
  int audio_index = -1, video_index = -1 ,i;
  is->videoStream=-1;
  is->audioStream=-1;
  global_video_state = is;
  callback.callback = decode_interrupt_cb;
  callback.opaque = is;
  if (avio_open2(&is->io_context, is->filename, 0, &callback, &io_dict)){
    fprintf(stderr, "Unable to open I/O for %s\n", is->filename);
    return -1;
  }

  // Open video file
  if(avformat_open_input(&pFormatCtx, is->filename, NULL, NULL)!=0) return -1; // Couldn't open file
  is->pFormatCtx = pFormatCtx;

  // Retrieve stream information
  if(avformat_find_stream_info(pFormatCtx, NULL)<0) return -1; // Couldn't find stream information

  // Dump information about file onto standard error
  av_dump_format(pFormatCtx, 0, is->filename, 0);
}

