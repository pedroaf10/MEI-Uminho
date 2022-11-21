<template>
  <div class="box">
    <q-scroll-area
      :thumb-style="thumbStyle"
      :bar-style="barStyle"
      class="areaPosts"
      ref="feedscroll"
    >
      <q-scroll-observer @scroll="updateSavedHeight" />
      <q-btn
        rounded
        icon="arrow_upward"
        label="Voltar ao Topo"
        class="btn_top"
        id="button_scrollTop"
        @click="scrollToTop()"
      />
      <q-card dark class="profile_card">
        <q-card-section v-if="friend" horizontal>
          <q-card-section class="left_zone">
            <q-avatar round size="100px">
              <q-img :src="friend.avatar.link" class="imagem_avatar" />
              <q-badge
                floating
                :color="friend.estado == 'Online' ? 'green' : 'grey'"
                rounded
                :label="friend.estado"
              />
            </q-avatar>

            <q-card-section>
              <q-item-section>
                <q-item-label style="font-weight: bold; font-size: 15px">
                  {{ friend.nome }}
                </q-item-label>
              </q-item-section>
            </q-card-section>

            <div v-if="isFriend != null">
              <q-btn
                v-if="isFriend === true"
                size="sm"
                class="button_remove_friend"
                @click="removeFriend"
                >Remover Amigo</q-btn
              >
              <q-btn
                v-else
                size="sm"
                class="button_adicionar_amigo"
                @click="adicionarAmigo"
                >Adicionar Amigo</q-btn
              >
            </div>

            <q-rating
              v-model="friend_classificacao"
              size="2em"
              max="5"
              :color="
                friend_classificacao > 4
                  ? 'green'
                  : friend_classificacao > 2
                  ? 'yellow'
                  : 'red'
              "
              readonly
            />

            <div
              style="display: flex; justify-content: center; margin-top: 5px"
            >
              <p style="font-weight: bold">Classificação:</p>
              <p
                :style="
                  'margin-left: 5px; font-weight: bold; color: ' +
                  (friend_classificacao > 4
                    ? 'green'
                    : friend_classificacao > 2
                    ? 'yellow'
                    : 'red')
                "
              >
                {{ friend_classificacao }}
              </p>
            </div>

            <div style="width: 80%; margin: auto; margin-top: 10px">
              <q-select
                outlined
                class="select_stuff"
                use-chips
                :disable="podeClassificar == false"
                v-model="classificar_user"
                :options="classificationOptions"
                :dense="dense"
                :options-dense="denseOpts"
                label="Classificar"
                label-color="secondary"
              >
                <template v-slot:prepend>
                  <q-icon name="star" color="secondary" />
                </template>
              </q-select>
            </div>

            <div class="row buttons">
              <div class="col-xs-12">
                <q-btn
                  size="sm"
                  class="button_save"
                  @click="classificar"
                  :disable="!podeClassificar || classificar_user == null"
                  >Classificar</q-btn
                >
                <q-tooltip
                  v-if="!podeClassificar"
                  class="bg-accent"
                  :offset="[0, 0]"
                >
                  <strong
                    >Já classificou ou ainda não jogou com este
                    utilizador</strong
                  >
                </q-tooltip>
              </div>
            </div>
          </q-card-section>

          <q-separator vertical />

          <q-card-section class="right_zone">
            <q-card-section horizontal class="icon_e_titulo">
              <q-icon size="40px" color="secondary" name="emoji_events" />
              <p class="recompensa">Recompensas</p>
            </q-card-section>

            <q-scroll-area
              :thumb-style="thumbStyle"
              :bar-style="barStyle"
              class="area_recompensas"
            >
              <q-list v-if="friend.recompensas.length > 0">
                <q-card-section
                  v-for="recompensa in friend.recompensas"
                  :key="recompensa"
                  horizontal
                  class="card_recompensa"
                >
                  <q-avatar size="40px">
                    <q-img :src="recompensa.imageLink" />
                  </q-avatar>

                  <p class="nome_recompensa">{{ recompensa.nome }}</p>
                  <q-tooltip class="bg-accent" :offset="[0, 0]">
                    <strong>{{ recompensa.descricao }}</strong>
                  </q-tooltip>
                </q-card-section>
              </q-list>
              <div v-else class="text-h6">Nenhuma recompensa para mostrar</div>
            </q-scroll-area>
          </q-card-section>
        </q-card-section>
      </q-card>
      <div
        v-if="friend"
        class="text-h5 text-secondary bg-dark text-bold q-py-md q-pl-lg my-posts"
      >
        Publicações de {{ friend.nome }}
      </div>
      <q-infinite-scroll
        ref="inf"
        @load="onLoad"
        :offset="100"
        v-if="game_posts.length"
      >
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
                  v-if="post.reacao === 'neutro' || post.reacao === 'dislike' || post.reacao == null"
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
                <q-item-section avatar>
                  <q-avatar size="50px">
                    <q-img
                      :src="post.gamer.avatar.link"
                      class="imagem_avatar_post"
                    />
                  </q-avatar>
                </q-item-section>

                <q-item-section>
                  <q-item-label
                    style="display: flex; justify-content: space-between"
                    ><div>{{ post.gamer.nome }}</div>
                  </q-item-label>
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
            <q-spinner-dots color="white" size="40px" />
          </div>
        </template>
      </q-infinite-scroll>
      <div v-else class="text-h6 text-white q-pa-md text-bold q-mx-sm no_posts">
        Não existem posts
      </div>
    </q-scroll-area>
  </div>
</template>

<script>
import { ref } from "@vue/reactivity";
import { computed, onMounted, onUpdated } from "@vue/runtime-core";
import { scroll } from "quasar";
const {
  setVerticalScrollPosition,
  getHorizontalScrollPosition,
  getVerticalScrollPosition,
} = scroll;
import axios from "axios";
import { useRoute } from "vue-router";
import URL from "../url.js";
import { useQuasar } from "quasar";

export default {
  setup() {
    const q = useQuasar();
    const classificar_user = ref(null);
    const disabled = ref(false);
    const podeClassificar = ref(null);
    const isFriend = ref(null);
    const inf = ref(null);
    const game_posts = ref([]);
    const saved_height = ref(0);
    const no_more_posts = ref(false);

    //variáveis aceder BD
    const friend = ref(null);
    const friend_classificacao = ref(null);
    const getParams = computed(() => {
      return route.params.id;
    });
    const route = useRoute();

    onMounted(async () => {
      //saber se o gajo é amigo ou não
      const me = await axios({
        method: "get",
        url: URL.URL + "/utilizador/getPerfil/" + localStorage.id,
      });

      const me_data = await me.data;
      const result = me_data.amigos.filter((u) => u.id == getParams.value);
      const size = result.length;

      if (size === 0) {
        isFriend.value = false;
      } else {
        isFriend.value = true;
      }

      //obter dados desse user
      const result_getPerfil = await axios({
        method: "get",
        url:
          URL.URL +
          "/utilizador/getPerfilGamer/" +
          localStorage.id +
          "/" +
          getParams.value,
      });

      const result_data_getPerfil = await result_getPerfil.data;
      friend.value = result_data_getPerfil.amigo;
      friend_classificacao.value = parseFloat(
        friend.value.classificacao.toFixed(2)
      );
      podeClassificar.value = result_data_getPerfil.pode_classificar;

      const game_feed = await axios({
        method: "get",
        url:
          URL.URL +
          "/posts/multimedia/postAmigo/" +
          localStorage.id +
          "/" +
          getParams.value +
          "/0",
      });

      ///multimedia/postAmigo/{id_gamer}/{id_amigo}/{pagina}

      const game_feed_data = await game_feed.data;
      game_posts.value = game_feed_data;
    }),
      onUpdated(async () => {
        //saber se o gajo é amigo ou não
        const me = await axios({
          method: "get",
          url: URL.URL + "/utilizador/getPerfil/" + localStorage.id,
        });

        const me_data = await me.data;
        const result = me_data.amigos.filter((u) => u.id == getParams.value);
        const size = result.length;

        if (size === 0) {
          isFriend.value = false;
        } else {
          isFriend.value = true;
        }

        //obter dados desse user
        const result_getPerfil = await axios({
          method: "get",
          url:
            URL.URL +
            "/utilizador/getPerfilGamer/" +
            localStorage.id +
            "/" +
            getParams.value,
        });

        const result_data_getPerfil = await result_getPerfil.data;
        friend.value = result_data_getPerfil.amigo;
        friend_classificacao.value = parseFloat(
          friend.value.classificacao.toFixed(2)
        );
        podeClassificar.value = result_data_getPerfil.pode_classificar;

        const game_feed = await axios({
          method: "get",
          url:
            URL.URL +
            "/posts/multimedia/postAmigo/" +
            localStorage.id +
            "/" +
            getParams.value +
            "/0",
        });

        ///multimedia/postAmigo/{id_gamer}/{id_amigo}/{pagina}

        const game_feed_data = await game_feed.data;
        game_posts.value = game_feed_data;
        });

    const feedscroll = ref(null);
    const scrollToTop = () => {
      const scrollArea = feedscroll.value;
      const scrollTarget = scrollArea.getScrollTarget();
      setTimeout(() => {
        setVerticalScrollPosition(scrollTarget, 0, 1000);
      }, 1);
      saved_height.value = 0;
      no_more_posts.value = false;
    };

    return {
      dense: ref(false),
      denseOpts: ref(false),
      thumbStyle: {
        right: "4px",
        borderRadius: "5px",
        backgroundColor: "#ffd208",
        width: "4px",
        opacity: 0.75,
      },
      barStyle: {
        right: "2px",
        borderRadius: "9px",
        width: "2px",
        opacity: 0.2,
      },
      openImage: ref(false),
      imagePopUp: ref(null),
      classificar_user,
      classificationOptions: [
        "1 Estrela",
        "2 Estrelas",
        "3 Estrelas",
        "4 Estrelas",
        "5 Estrelas",
      ],
      q,
      saved_height,
      no_more_posts,
      friend,
      friend_classificacao,
      getParams,
      disabled,
      podeClassificar,
      scrollToTop,
      feedscroll,
      isFriend,
      inf,
      game_posts,
      onLoad(index, done) {
        if (index - 1 === 0) {
          done();
        } else {
          setTimeout(async () => {
            const game_feed = await axios({
              method: "get",
              url:
                URL.URL +
                "/posts/postsMediaGamer/" +
                getParams.value +
                "/" +
                (index - 1),
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
    async classificar() {
      const cl = this.classificar_user.split(" ");

      await axios({
        method: "post",
        url:
          URL.URL +
          "/utilizador/avaliaGamer/" +
          localStorage.id +
          "/" +
          this.getParams,
        params: {
          classificacao: cl[0],
        },
      });

      //opcional
      const result_getPerfil = await axios({
        method: "get",
        url:
          URL.URL +
          "/utilizador/getPerfilGamer/" +
          localStorage.id +
          "/" +
          this.getParams,
      });

      const result_data_getPerfil = await result_getPerfil.data;
      this.friend = result_data_getPerfil.amigo;
      this.friend_classificacao = parseFloat(
        this.friend.classificacao.toFixed(2)
      );

      this.podeClassificar = false;
      this.classificar_user = null;
      this.q.notify({
        progress: true,
        message: "Classificação atribuída com sucesso!",
        color: "green",
        position: "bottom-right",
      });
    },

    async removeFriend() {
      this.$emit("friend_to_remove", this.friend.id);
      this.isFriend = false;
    },

    async adicionarAmigo() {
      this.$emit("friend_to_add", this.friend.nome);
      this.isFriend = true;
    },

    cancel() {
      this.$router.go(-1);
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
        this.q.notify({
          progress: true,
          message: "Like Registado com Sucesso",
          color: "green",
          position: "bottom-right",
        });
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
        this.q.notify({
          progress: true,
          message: "Dislike Registado com Sucesso",
          color: "green",
          position: "bottom-right",
        });
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
        const game_feed = await axios({
          method: "get",
          url: URL.URL + "/posts/postsMediaGamer/" + newVal + "/0",
        });

        const game_feed_data = await game_feed.data;
        this.game_posts = game_feed_data;

        if (this.inf) {
          this.inf.reset();
          this.inf.resume();
        }
      }
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
.box {
  margin-bottom: -30px;
}

.areaPosts {
  height: 92vh;
}

.profile_card {
  width: 80%;
  margin: auto;
  margin-top: 5%;
  margin-bottom: 2%;
}

.left_zone {
  text-align: center;
  background: #1d1d1d;
  margin-top: 1%;
  width: 290px;
}

.right_zone {
  width: 80%;
  height: 500px;
  background: #1d1d1d;
}

.upload_file {
  margin: 20px auto;
  border-radius: 5pt;
  background: #222222;
}

.upload_file label {
  width: 600px;
}

.zona_tags {
  display: flex;
}

.reset_avatar {
  width: 150px;
  height: 20px;
  font-size: 12px;
  margin-top: 10px;
  font-weight: bold;
}

.reset_avatar:hover {
  background: #ffd208;
  transform: scale(1.05);
  color: black;
}

.change_avatar {
  margin-top: 20px;
  background: grey;
  width: 50%;
}

.username {
  font-weight: bold;
  margin-top: -20px;
}

.area_recompensas {
  height: 80%;
  padding: 20px;
  background: #222222;
  border-radius: 10px;
}

.recompensa_card {
  color: white;
  padding-left: 10px;
  padding-top: 5px;
  padding-bottom: 1px;
  margin-bottom: 20px;
  border-radius: 15px;
}

.titulo {
  font-weight: bold;
  font-size: 18px;
}

.avaliacao {
  margin-bottom: 10px;
  font-weight: bold;
}

.icon_e_titulo {
  margin-top: 1%;
  margin-left: 2%;
}

.card_recompensa {
  background: #1d1d1d;
  border-radius: 10px;
  justify-content: center;
  padding-top: 10px;
  margin-top: 10px;
  padding-bottom: 5px;
}

.recompensa {
  margin-top: 1%;
  margin-left: 2%;
  font-weight: bold;
  font-size: 20px;
}

.nome_recompensa {
  margin-top: 1.5%;
  margin-left: 2%;
  font-weight: bold;
  font-size: 15px;
}

.buttons {
  margin-top: 40px;
}

.button_cancel {
  background: red;
  color: white;
  font-weight: bold;
  margin-bottom: 10px;
  margin-right: 10px;
}

.button_cancel:hover {
  transform: scale(1.1);
}

.button_save {
  background: #005cc5;
  font-weight: bold;
}

.button_save:disabled {
  background: grey;
}

.button_remove_friend {
  margin-bottom: 30px;
  background: red;
  font-weight: bold;
}

.button_remove_friend:disabled {
  background: #222222;
}

.button_remove_friend:hover {
  transform: scale(1.1);
}

.button_adicionar_amigo {
  margin-bottom: 30px;
  background: #005cc5;
  font-weight: bold;
}

.button_adicionar_amigo:hover {
  transform: scale(1.1);
}

.button_classificar {
  margin: auto;
  background: #434649;
  font-weight: bold;
}

.button_classificar:hover {
  transform: scale(1.1);
}

.button_save:hover {
  transform: scale(1.1);
}

.imagem_avatar {
  width: 100px;
  height: 100px;
}

.select_stuff {
  outline: none;
  border: none;
  border-radius: 5pt;
  box-shadow: 0 0 0 2px #ffd208;
}

.my-card {
  width: 80%;
  margin: 15px auto;
  align-items: center;
  border-radius: 20px;
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

.content {
  width: 100%;
}

.imagem_avatar_post {
  width: 50px;
  height: 50px;
}

.data {
  font-size: 12px;
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
.descricao {
  color: white;
  word-break: break-all;
  hyphens: auto;
  white-space: pre-line;
}

.box_img {
  max-width: 100%;
  max-height: 500px;
  border-radius: 10px;
}

.my-posts {
  width: 80%;
  margin: 15px auto;
  align-items: center;
  border-radius: 20px;
}

.no_posts {
  width: 80%;
  margin: auto;
  margin-top: 10px;
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

@media only screen and (max-height: 900px) {
  .areaPosts {
    height: 90vh;
  }
}
</style>
