<template>
  <div class="box">
    <div class="q-pa-sm">
      <q-carousel
        v-if="jogosPopulares.length > 0"
        animated
        v-model="slide"
        navigation
        swipeable
        infinite
        :autoplay="autoplay"
        arrows
        class="carrosel"
        transition-prev="slide-right"
        transition-next="slide-left"
        @mouseenter="autoplay = false"
        @mouseleave="autoplay = true"
      >
        <q-carousel-slide
          v-for="(jogo, index) in jogosPopulares"
          :key="jogo.jogo.id"
          :name="jogo.jogo.id"
          :img-src="jogo.jogo.bannerLink"
        >
          <div class="absolute-bottom custom-caption">
            <div class="caption-text">
              {{ jogo.jogo.nome }}
            </div>

            <div class="row items-center">
              <span class="caption-text q-mr-md"
                >{{ jogo.numSeguidores }} Membros</span
              >

              <q-btn
                class="caption-button q-ma-none"
                :disabled="disabledButtons[index].disabled"
                @click="addGame(jogo.jogo)"
              >
                Seguir Jogo
              </q-btn>
            </div>
          </div>
        </q-carousel-slide>
      </q-carousel>
    </div>
    <q-separator />
    <div
      class="text-h5 text-secondary q-pa-md text-bold bg-dark q-mx-sm q-pl-xl"
    >
      Publicações Populares
    </div>
    <q-card
      v-for="post in postsPopulares"
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
              <q-avatar size="50px" @click="viewFriendProfile(post.gamer.id)">
                <q-img :src="post.gamer.avatar.link" class="imagem_avatar" />
              </q-avatar>
              <q-tooltip class="bg-accent" :offset="[0, 0]">
                <strong>Ver Perfil Utilizador</strong>
              </q-tooltip>
            </q-item-section>

            <q-item-section>
              <q-item-label>{{ post.gamer.nome }}</q-item-label>
              <q-item-label class="data">
                {{ time_upload(post.datetime) }}
              </q-item-label>
              <q-item-label class="text-bold text-secondary">{{
                post.jogo
              }}</q-item-label>
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
              <video v-if="isVideo(post.multimedia)" controls class="box_img">
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
  </div>
</template>

<script>
import { onBeforeMount, onMounted, ref } from "vue";
import axios from "axios";
import URL from "../url.js";
import { useQuasar } from "quasar";
export default {
  setup() {
    const q = useQuasar();
    const postsPopulares = ref([]);
    const jogosPopulares = ref([]);
    const slide = ref(0);
    const disabledButtons = ref([]);
    const myGames = ref([]);

    onMounted(async () => {
      const result = await axios({
        method: "get",
        url: URL.URL + "/posts/postsMultimedia/10/" + localStorage.id,
      });
      const result_data = await result.data;
      postsPopulares.value = result_data;

      const result2 = await axios({
        method: "get",
        url: URL.URL + "/posts/getListaJogosPopulares",
        params: {
          limit: 4,
        },
      });
      const result_data2 = await result2.data;
      jogosPopulares.value = result_data2;

      const games = await axios({
        method: "get",
        url: URL.URL + "/utilizador/getListaJogosSeguir/" + localStorage.id,
      });
      const games_data = await games.data;
      myGames.value = games_data;

      slide.value = jogosPopulares.value[0].jogo.id;
      jogosPopulares.value.forEach((item) =>
        myGames.value.filter((e) => e.id === item.jogo.id).length > 0
          ? disabledButtons.value.push({ game: item.jogo.id, disabled: true })
          : disabledButtons.value.push({ game: item.jogo.id, disabled: false })
      );
    });

    return {
      openImage: ref(false),
      q,
      slide,
      autoplay: ref(true),
      imagePopUp: ref(null),
      postsPopulares,
      jogosPopulares,
      disabledButtons,
    };
  },
  methods: {
    async addGame(game) {
      this.disabledButtons.map((el) => {
        if (el.game === game.id) {
          el.disabled = true;
        }
      });
      const result = [];
      result.push(game);
      const data = [game.id];

      const res = await axios({
        method: "post",
        url: URL.URL + "/utilizador/addJogoSeguir/" + localStorage.id,
        data: {
          jogos: data,
        },
      });
      const res_data = await res.data;
      if (res_data == true) {
        this.jogosPopulares.forEach((item) => {
          if (item.jogo.id === game.id) {
            item.numSeguidores = item.numSeguidores + 1;
          }
        });
      }
      this.$emit("gamesToAdd", result);
    },

    isVideo(multimedia) {
      const last = multimedia.split(".").pop();

      if (last == "mp4" || last == "mp3") return true;
      else return false;
    },

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

    async likePost(id) {
      const btn = this.postsPopulares.filter((p) => p.id == id)[0];

      if (btn.reacao == "like") {
        await axios({
          method: "post",
          url: URL.URL + "/posts/like/remove/" + id + "/" + localStorage.id,
        });
        this.postsPopulares
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
          this.postsPopulares
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

          this.postsPopulares
            .filter((p) => p.id == id)
            .forEach((p) => {
              p.reacao = "like";
              p.likes += 2;
            });
        }
        this.q.notify({
          progress: true,
          message: "Like Registado com Sucesso",
          color: "green",
          position: "bottom-right",
        });
      }
    },
    async dislikePost(id) {
      const btn = this.postsPopulares.filter((p) => p.id == id)[0];

      if (btn.reacao == "dislike") {
        await axios({
          method: "post",
          url: URL.URL + "/posts/dislike/remove/" + id + "/" + localStorage.id,
        });
        this.postsPopulares
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

          this.postsPopulares
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

          this.postsPopulares
            .filter((p) => p.id == id)
            .forEach((p) => {
              p.reacao = "dislike";
              p.likes -= 2;
            });
        }
        this.q.notify({
          progress: true,
          message: "Dislike Registado com Sucesso",
          color: "green",
          position: "bottom-right",
        });
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
  },
};
</script>

<style scoped>
.box {
  margin-bottom: -30px;
}

.carrosel {
  height: 190px;
  width: 100%;
}

@media only screen and (max-width: 1400px) {
  .carrosel {
    height: 150px;
  }
  .caption-text {
    font-size: 20px !important;
  }
  .caption-button {
    height: 20px !important;
    width: 120px !important;
  }

  .custom-caption {
    padding: 8px !important;
  }
}

@media only screen and (max-width: 1200px) {
  .carrosel {
    height: 110px;
  }
  .caption-text {
    font-size: 15px !important;
  }
  .caption-button {
    height: 15px !important;
    width: 120px !important;
    font-size: 12px !important;
  }

  .custom-caption {
    padding: 6px !important;
  }
}

@media only screen and (max-width: 1000px) {
  .carrosel {
    height: 70px;
  }

  .caption-text {
    font-size: 12px !important;
  }
  .caption-button {
    height: 10px !important;
    width: 100px !important;
    font-size: 10px !important;
  }

  .custom-caption {
    padding: 3px !important;
  }
}

.custom-caption {
  z-index: 10;
  display: flex;
  justify-content: space-between;
  align-items: center;
  padding: 12px;
  color: white;
  background-color: rgba(0, 0, 0, 0.3);
}

.caption-text {
  font-size: 25px;
}

.caption-button {
  height: 30px;
  width: 120px;
  font-weight: bold;
}

.caption-button:hover {
  transform: scale(1.05);
  background: #ffd208;
  color: black;
  font-weight: bold;
}

.avatar {
  height: 50px;
  width: 50px;
}

.areaPosts {
  height: 100%;
  padding-left: 5%;
  padding-right: 5%;
}

.my-card {
  width: 90%;
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

.like_number {
  align-items: center;
  font-weight: bold;
  font-size: 20px;
  margin-top: -40px;
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

.post_user {
  cursor: pointer;
}

.post_user:hover {
  transform: scale(1.1);
}

a:hover {
  transform: scale(1.05);
}

a:link {
  text-decoration: none;
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
</style>
