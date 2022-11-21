<template>
  <div class="box">
    <div class="filter_zone row">
      <div class="col-8 row column-xs">
        <div class="row items-center">
          <div
            class="text-h7 text-white text-bold q-mr-none q-ml-md q-pl-xl"
            style=""
          >
            Filtros:
          </div>

          <q-btn
            v-if="selectedFilter == 'datetime'"
            rounded
            icon="calendar_month"
            label="Data"
            class="bg-secondary text-black btn_filtro"
          />
          <q-btn
            v-else
            rounded
            icon="calendar_month"
            label="Data"
            class="btn_filtro"
            @click="selectDate"
          />
          <q-btn
            v-if="selectedFilter == 'datetime'"
            rounded
            icon="calendar_month"
            class="bg-secondary text-black btn_filtro_small"
          />
          <q-btn
            v-else
            rounded
            icon="calendar_month"
            class="btn_filtro_small"
            @click="selectDate"
          />

          <q-btn
            v-if="selectedFilter == 'likes'"
            rounded
            icon="thumb_up"
            label="Likes"
            class="bg-secondary text-black btn_filtro"
          />

          <q-btn
            v-else
            rounded
            icon="thumb_up"
            label="Likes"
            class="btn_filtro"
            @click="selectLikes"
          />

          <q-btn
            v-if="selectedFilter == 'likes'"
            rounded
            icon="thumb_up"
            class="bg-secondary text-black btn_filtro_small"
          />

          <q-btn
            v-else
            rounded
            icon="thumb_up"
            class="btn_filtro_small"
            @click="selectLikes"
          />
        </div>
        <div class="row items-center order-by">
          <div class="text-h7 text-white text-bold q-mr-none q-ml-md q-pl-xl">
            Ordenar:
          </div>
          <q-btn
            v-if="selected_order == 'ASC'"
            rounded
            icon="arrow_upward"
            :label="
              selectedFilter == 'datetime' ? 'Mais Recente' : 'Ascendente'
            "
            class="btn_filtro"
            @click="invert_order"
          />
          <q-btn
            v-else
            rounded
            icon="arrow_downward"
            :label="
              selectedFilter == 'datetime' ? 'Mais Antigo' : 'Descendente'
            "
            class="btn_filtro"
            @click="invert_order"
          />
          <q-btn
            v-if="selected_order == 'ASC'"
            rounded
            icon="arrow_upward"
            class="btn_filtro_small"
            @click="invert_order"
          />
          <q-btn
            v-else
            rounded
            icon="arrow_downward"
            class="btn_filtro_small"
            @click="invert_order"
          />
        </div>
      </div>
      <div class="col-4 q-pl-xl">
        <q-btn
          rounded
          label="Deixar de seguir jogo"
          class="btn_stop_follow"
          @click="openPromtp = true"
        />
      </div>
    </div>
    <q-dialog v-model="openPromtp" persistent>
      <q-card class="bg-dark">
        <q-card-section class="row items-center">
          <q-avatar icon="warning" color="primary" text-color="white" />
          <span class="q-ml-sm text-white">
            Tem a certeza que quer deixar de seguir este jogo?</span
          >
        </q-card-section>

        <q-card-actions align="right">
          <q-btn outline color="secondary" label="Cancelar" v-close-popup />
          <q-btn
            outline
            color="secondary"
            label="Confirmar"
            @click="removeGame"
            v-close-popup
          />
        </q-card-actions>
      </q-card>
    </q-dialog>

    <q-scroll-area
      :thumb-style="thumbStyle"
      :bar-style="barStyle"
      class="areaPosts"
      ref="feedscroll"
      @scroll="updateSavedHeight"
    >
      <q-btn
        rounded
        icon="arrow_upward"
        label="Voltar ao Topo"
        class="btn_top"
        id="button_scrollTop"
        @click="scrollToTop()"
      />
      <q-infinite-scroll ref="inf" @load="onLoad" :offset="100">
        <q-card
          v-for="post in game_posts"
          :key="post"
          dark
          class="bg-grey-9 my-card"
        >
          <q-card-section horizontal>
            <q-card-section class="like_zone">
              <q-item>
                <q-btn
                  v-if="post.reacao == 'neutro' || post.reacao == 'dislike'"
                  flat
                  round
                  icon="thumb_up"
                  @click="likePost(post.id)"
                />
                <q-btn
                  v-if="post.reacao == 'like'"
                  flat
                  round
                  icon="thumb_up"
                  style="color: #00c230"
                  @click="likePost(post.id)"
                >
                </q-btn>
              </q-item>
              <q-item>
                <q-item-section
                  style="
                    align-items: center;
                    font-weight: bold;
                    font-size: 20px;
                    color: white;
                  "
                >
                  {{ post.likes }}
                </q-item-section>
              </q-item>
              <q-item>
                <q-btn
                  v-if="post.reacao == 'neutro' || post.reacao == 'like'"
                  flat
                  round
                  icon="thumb_down"
                  @click="dislikePost(post.id)"
                >
                </q-btn>
                <q-btn
                  v-if="post.reacao == 'dislike'"
                  flat
                  round
                  icon="thumb_down"
                  style="color: red"
                  @click="dislikePost(post.id)"
                >
                </q-btn>
              </q-item>
            </q-card-section>

            <q-separator vertical></q-separator>

            <q-card-section class="content">
              <q-item>
                <q-item-section class="post_user" avatar>
                  <q-avatar
                    size="50px"
                    @click="viewFriendProfile(post.gamer.id)"
                  >
                    <q-img
                      :src="post.gamer.avatar.link"
                      class="imagem_avatar"
                    />
                  </q-avatar>
                  <q-tooltip class="bg-accent" :offset="[10, 0]">
                    <strong>Ver Perfil Utilizador</strong>
                  </q-tooltip>
                </q-item-section>

                <q-item-section>
                  <q-item-label>{{ post.gamer.nome }}</q-item-label>
                  <q-item-label class="data">
                    {{ time_upload(post.datetime) }}
                  </q-item-label>
                  <div class="zona_tags">
                    <q-item-label v-for="t in post.tags" :key="t" class="tag">
                      #{{ t.tag }}
                    </q-item-label>
                  </div>
                </q-item-section>
              </q-item>

              <q-separator />

              <q-item class="descricao">
                <div
                  v-if="post.tags.length > 0 && post.tags[0].tag == 'NEWS'"
                  class="text-h6"
                >
                  <div class="text-h6">{{ newsText(post.descricao)[0] }}</div>
                  <div class="flex text-h7">
                    <div>Para mais informações, ler&nbsp;</div>
                    <a
                      :href="newsText(post.descricao)[1]"
                      target="_blank"
                      style="color: #ffd208"
                      >artigo</a
                    >
                  </div>
                  <div style="font-size: 15px">
                    Autor: {{ newsText(post.descricao)[2] }}
                  </div>
                  <div style="font-size: 15px">
                    Fonte: {{ newsText(post.descricao)[3] }}
                  </div>
                </div>
                <div v-else class="text-h6">
                  {{ post.descricao }}
                </div>
              </q-item>

              <q-item v-if="post.multimedia">
                <q-item-section>
                  <video
                    v-if="isVideo(post.multimedia)"
                    controls
                    class="box_img"
                  >
                    <source :src="post.multimedia" type="video/mp4" />
                    Your browser does not support HTML video.
                  </video>
                  <q-img
                    v-else
                    :src="post.multimedia"
                    class="box_img cursor-pointer"
                    @click="
                      openImage = true;
                      imagePopUp = post.multimedia;
                    "
                  />
                </q-item-section>
              </q-item>
            </q-card-section>
          </q-card-section>
        </q-card>
        <q-dialog v-model="openImage">
          <q-img :src="imagePopUp" fit="contain" class="bg-dark popupimg">
            <div class="no-margin no-padding divclose">
              <q-btn
                round
                class="absolute-left-right closeimg"
                @click="openImage = false"
              >
                <q-avatar size="20px">
                  <q-icon name="close" class="closeimgicon" />
                </q-avatar>
              </q-btn>
            </div>
          </q-img>
        </q-dialog>
        <template v-slot:loading>
          <div class="row justify-center q-my-md">
            <q-spinner-dots color="secondary" size="40px" />
          </div>
        </template>
      </q-infinite-scroll>
    </q-scroll-area>
  </div>
</template>

<script>
import { ref } from "@vue/reactivity";
import axios from "axios";
import { computed, onMounted, onUpdated } from "@vue/runtime-core";
import { scroll } from "quasar";
const {
  setVerticalScrollPosition,
  getHorizontalScrollPosition,
  getVerticalScrollPosition,
} = scroll;
import { useRoute } from "vue-router";
import URL from "../url.js";
import { useQuasar } from "quasar";
export default {
  name: "GameFeed",
  setup(props, { emit }) {
    const q = useQuasar();
    const selectedFilter = ref("datetime");
    const selected_order = ref("ASC");
    const saved_height = ref(0);
    const no_more_posts = ref(false);
    const openPromtp = ref(false);
    const route = useRoute();
    const inf = ref(null);
    const linkTo = (link) => {
      return require("../assets/imagens/" + link);
    };

    //dados obtidos da base de dados
    const game_posts = ref([]);

    const getParams = computed(() => {
      return route.params.id;
    });

    onMounted(async () => {
      //obter os posts de um determinado jogo
      const game_feed = await axios({
        method: "get",
        url:
          URL.URL +
          "/posts/multimedia/" +
          localStorage.id +
          "/" +
          getParams.value +
          "/0/" +
          selectedFilter.value +
          "/" +
          selected_order.value,
      });

      const game_feed_data = await game_feed.data;
      game_posts.value = game_feed_data;
    });

    const feedscroll = ref(null);
    const scrollToTop = () => {
      saved_height.value = 0;
      no_more_posts.value = false;

      const scrollArea = feedscroll.value;
      const scrollTarget = scrollArea.getScrollTarget();
      setTimeout(() => {
        setVerticalScrollPosition(scrollTarget, 0, 1000);
      }, 1);
    };

    const removeGame = () => {
      q.notify({
        progress: true,
        message: "Jogo removido com sucesso!",
        color: "green",
        position: "bottom-right",
      });
      emit("stopFollowing", getParams.value);
    };

    return {
      dense: ref(false),
      denseOpts: ref(false),
      thumbStyle: {
        right: "4px",
        borderRadius: "5px",
        backgroundColor: "#ffd208",
        width: "4px",
      },
      barStyle: {
        right: "2px",
        borderRadius: "9px",
        width: "2px",
        opacity: 0.8,
      },
      q,
      no_more_posts,
      selectedFilter,
      selected_order,
      inf,
      linkTo,
      game_posts,
      getParams,
      feedscroll,
      scrollToTop,
      saved_height,
      openImage: ref(false),
      imagePopUp: ref(null),
      openPromtp,
      removeGame,
      onLoad(index, done) {
        if (index - 1 === 0) {
          done();
        } else {
          setTimeout(async () => {
            const game_feed = await axios({
              method: "get",
              url:
                URL.URL +
                "/posts/multimedia/" +
                localStorage.id +
                "/" +
                getParams.value +
                "/" +
                (index - 1) +
                "/" +
                selectedFilter.value +
                "/" +
                selected_order.value,
            });

            const game_feed_data = await game_feed.data;
            if (game_feed_data.length == 0) {
              no_more_posts.value = true;
              done(true);
            }
            game_posts.value.push(...game_feed_data);

            done();
          }, 1000);
        }
      },
    };
  },
  methods: {
    time_upload(data) {
      const data_publicacao = new Date(data);
      const data_atual = Date.now();
      const diff = data_atual - data_publicacao;

      //const segundos
      const valor_segundos = (diff / 1000).toFixed(0);

      if (valor_segundos < 60) {
        if (valor_segundos < 30) {
          return "Agora mesmo";
        } else {
          return "Há " + valor_segundos + " segundos";
        }
      } else {
        //em minutos
        const valor_minutos = (Math.abs(diff) / 1000 / 60).toFixed(0);

        if (valor_minutos < 60) {
          return "Há " + valor_minutos + " minutos";
        } else {
          //em horas
          const valor_horas = (Math.abs(diff) / 36e5).toFixed(0);

          if (valor_horas == 1) {
            return "Há " + valor_horas + " hora";
          }

          if (valor_horas < 24) {
            return "Há " + valor_horas + " horas";
          } else {
            //em dias
            const valor_dias = (diff / (1000 * 3600 * 24)).toFixed(0);

            if (valor_dias < 2) return "Há " + valor_dias + " dia";
            else return "Há " + valor_dias + " dias";
          }
        }
      }
    },

    invert_order() {
      if (this.selected_order == "ASC") {
        this.selected_order = "DESC";
      } else {
        this.selected_order = "ASC";
      }
    },

    selectDate() {
      if (this.selectedFilter != "datetime") this.selectedFilter = "datetime";
    },

    selectLikes() {
      if (this.selectedFilter != "likes") this.selectedFilter = "likes";
    },

    isVideo(multimedia) {
      const last = multimedia.split(".").pop();

      if (last == "mp4" || last == "mp3") return true;
      else return false;
    },

    async likePost(id) {
      const btn = this.game_posts.filter((p) => p.id == id)[0];

      if (btn.reacao == "like") {
        (await axios({
          method: "post",
          url: URL.URL + "/posts/like/remove/" + id + "/" + localStorage.id,
        })) *
          this.game_posts
            .filter((p) => p.id == id)
            .forEach((p) => {
              p.reacao = "neutro";
              p.likes -= 1;
            });
      } else {
        if (btn.reacao == "neutro") {
          await axios({
            method: "post",
            url: URL.URL + "/posts/like/" + id + "/" + localStorage.id,
          });
          this.game_posts
            .filter((p) => p.id == id)
            .forEach((p) => {
              p.reacao = "like";
              p.likes += 1;
            });
        } else {
          await axios({
            method: "post",
            url: URL.URL + "/posts/like/" + id + "/" + localStorage.id,
          });

          await axios({
            method: "post",
            url: URL.URL + "/posts/like/" + id + "/" + localStorage.id,
          });

          this.game_posts
            .filter((p) => p.id == id)
            .forEach((p) => {
              p.reacao = "like";
              p.likes += 2;
            });
        }
      }
    },

    async dislikePost(id) {
      const btn = this.game_posts.filter((p) => p.id == id)[0];

      if (btn.reacao == "dislike") {
        await axios({
          method: "post",
          url: URL.URL + "/posts/dislike/remove/" + id + "/" + localStorage.id,
        });
        this.game_posts
          .filter((p) => p.id == id)
          .forEach((p) => {
            p.reacao = "neutro";
            p.likes += 1;
          });
      } else {
        if (btn.reacao == "neutro") {
          await axios({
            method: "post",
            url: URL.URL + "/posts/dislike/" + id + "/" + localStorage.id,
          });

          this.game_posts
            .filter((p) => p.id == id)
            .forEach((p) => {
              p.reacao = "dislike";
              p.likes -= 1;
            });
        } else {
          await axios({
            method: "post",
            url: URL.URL + "/posts/dislike/" + id + "/" + localStorage.id,
          });

          await axios({
            method: "post",
            url: URL.URL + "/posts/dislike/" + id + "/" + localStorage.id,
          });

          this.game_posts
            .filter((p) => p.id == id)
            .forEach((p) => {
              p.reacao = "dislike";
              p.likes -= 2;
            });
        }
      }
    },
    viewFriendProfile(id) {
      if (id == localStorage.id) {
        this.$router.push("/profile");
      } else {
        this.$router.push("/friendProfile/" + id);
      }
    },
    newsText(text) {
      const res = text.split("\n");
      return res;
    },
    updateSavedHeight() {
      const scrollArea = this.feedscroll;
      const scrollTarget = scrollArea.getScrollTarget();
      this.saved_height = getVerticalScrollPosition(scrollTarget);
    },
  },
  watch: {
    async getParams(newVal) {
      if (newVal) {
        this.scrollToTop();
        const game_feed = await axios({
          method: "get",
          url:
            URL.URL +
            "/posts/multimedia/" +
            localStorage.id +
            "/" +
            newVal +
            "/0",
        });

        const game_feed_data = await game_feed.data;
        this.game_posts = game_feed_data;

        if (this.inf) {
          this.inf.reset();
          this.inf.resume();
        }
      }
    },

    async selectedFilter(newVal) {
      this.scrollToTop();
      const game_feed = await axios({
        method: "get",
        url:
          URL.URL +
          "/posts/multimedia/" +
          localStorage.id +
          "/" +
          this.getParams +
          "/0/" +
          newVal +
          "/" +
          this.selected_order,
      });

      const game_feed_data = await game_feed.data;
      this.game_posts = game_feed_data;

      this.inf.reset();
      this.inf.resume();
    },

    async selected_order(newVal) {
      this.scrollToTop();
      const game_feed = await axios({
        method: "get",
        url:
          URL.URL +
          "/posts/multimedia/" +
          localStorage.id +
          "/" +
          this.getParams +
          "/0/" +
          this.selectedFilter +
          "/" +
          newVal,
      });

      const game_feed_data = await game_feed.data;
      this.game_posts = game_feed_data;

      this.inf.reset();
      this.inf.resume();
    },

    saved_height(newVal) {
      if (newVal > 2600)
        document.getElementById("button_scrollTop").style.display = "block";
      else document.getElementById("button_scrollTop").style.display = "none";
    },

    no_more_posts(newVal) {
      if (newVal == true) {
        this.q.notify({
          progress: true,
          message: "Não há mais Posts para Mostrar",
          color: "grey",
          position: "bottom-right",
        });
      }
    },
  },
};
</script>

<style scoped>
.avatar {
  height: 50px;
  width: 50px;
}

.areaPosts {
  height: 84vh;
  padding-left: 5%;
  padding-right: 5%;
}

.my-card {
  margin: 15px auto;
  align-items: center;
  border-radius: 20px;
}

.content {
  width: 100%;
}

.like_zone {
  background: rgb(32, 32, 32);
  align-items: center;
}

.box_img {
  max-width: 100%;
  max-height: 500px;
  border-radius: 10px;
}

.zona_tags {
  display: flex;
}

.tag {
  margin-right: 10px;
  margin-top: 5px;
  border-radius: 10px;
  font-size: 15px;
  color: #ffd208;
  cursor: pointer;
  background: #1d1d1d;
  padding: 5px;
}

.tag:hover {
  transform: scale(1.05);
}

.data {
  font-size: 12px;
}

.descricao {
  color: white;
  word-break: break-all;
  hyphens: auto;
  white-space: pre-line;
}

.imagem_avatar {
  width: 50px;
  height: 50px;
}

.filter_zone {
  position: -webkit-sticky;
  position: sticky;
  z-index: 2;
  background: #222222;
  align-items: center;

  padding-top: 20px;
  padding-bottom: 20px;
}

.select_stuff {
  outline: none;
  border: none;
  border-radius: 5pt;
  box-shadow: 0 0 0 2px #ffd208;
  width: 100%;
}

.sort_button {
  outline: none;
  border: none;
  border-radius: 5pt;
  box-shadow: 0 0 0 2px #ffd208;
  width: 100%;
  height: 100%;
  margin-left: 20px;
  color: #ffd208;
  font-weight: bold;
}

.sort_button:hover {
  background: #ffd208;
  color: #1d1d1d;
}

.btn_filtro {
  outline: none;
  border: none;
  border-radius: 5pt;
  box-shadow: 0 0 0 2px #ffd208;
  height: 100%;
  margin-left: 20px;
  color: #ffd208;
  font-weight: bold;
}

.btn_filtro:hover {
  background: #ffd208;
  color: black;
  box-shadow: 0 0 0 2px black;
}

.btn_filtro_small {
  display: none;
  outline: none;
  border: none;
  border-radius: 5pt;
  box-shadow: 0 0 0 2px #ffd208;
  height: 100%;
  margin-left: 20px;
  color: #ffd208;
  font-weight: bold;
}

.btn_filtro_small:hover {
  background: #ffd208;
  color: black;
  box-shadow: 0 0 0 2px black;
}

.btn_stop_follow {
  outline: none;
  border: none;
  border-radius: 5pt;
  box-shadow: 0 0 0 2px red;
  height: 100%;
  margin-left: 20%;
  color: red;
  font-weight: bold;
}

.btn_stop_follow:hover {
  background: red;
  color: black;
  box-shadow: 0 0 0 2px black;
}

.btn_top {
  position: fixed;
  z-index: 10;
  margin-top: 1%;
  margin-left: 38%;
  background: #005cc5;
  color: white;
  font-weight: bold;
  display: none;
  opacity: 0.9;
}

.btn_top:hover {
  transform: scale(1.05);
}

.post_user {
  cursor: pointer;
}

.post_user:hover {
  transform: scale(1.1);
}

.popupimg {
  max-width: 80%;

  width: 100%;
  border-radius: 20px;
  overflow: hidden;
}

.closeimg {
  background-color: rgba(1, 1, 1, 0.5);
}

.closeimgicon {
  color: #ffd208;
}

.divclose {
  background-color: rgba(0, 0, 0, 0);
}

.row.items-center > .text-h7 {
  width: 100px;
}

@media only screen and (max-width: 1399px) {
  .order-by {
    margin-top: 10px;
  }
  .btn_stop_follow {
    margin-left: 0%;
  }
}

@media only screen and (max-width: 1000px) {
  .btn_filtro_small {
    display: block;
  }
  .btn_filtro {
    display: none;
  }
}

@media only screen and (max-height: 900px) {
  .areaPosts {
    height: 79vh;
  }
  .btn_stop_follow {
    margin-right: 10%;
  }
}
</style>
