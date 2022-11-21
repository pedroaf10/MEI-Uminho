<template>
  <div class="bg-dark box">
    <img src="../assets/register/epicgames.png" class="epic_games_logo" />
    <img src="../assets/register/controller.png" class="abs" />
    <img src="../assets/register/headset.png" class="abs2" />
    <div class="row">
      <div class="register">
        <img src="../assets/logo.png" class="logo" />
        <q-card dark class="bg-primary my-card">
          <q-card-section class="q-pb-xs q-pt-xs">
            <div class="text">Criar conta</div>
          </q-card-section>

          <q-separator dark inset />

          <q-scroll-area
            :thumb-style="thumbStyle"
            :bar-style="barStyle"
            class="box_campos"
          >
            <q-card-section class="q-pb-xs">
              <q-input
                class="input_stuff"
                v-model="state.username"
                outlined
                dense
                label="Username"
                color="secondary"
                label-color="secondary"
                input-style="color:white"
              />
              <span v-if="v$.username.$error" class="error-msg">
                *Campo obrigatório
              </span>
            </q-card-section>
            <q-card-section class="q-pb-xs q-pt-xs">
              <q-input
                class="input_stuff"
                v-model="state.email"
                outlined
                dense
                label="Email"
                color="secondary"
                label-color="secondary"
                input-style="color:white"
              />
              <span v-if="v$.email.$error" class="error-msg">
                *Insira um e-mail válido
              </span>
            </q-card-section>
            <q-card-section class="q-pb-xs q-pt-xs">
              <q-input
                class="input_stuff"
                v-model="state.password.password"
                outlined
                dense
                type="password"
                label="Password"
                color="secondary"
                label-color="secondary"
                input-style="color:white"
              />
              <span v-if="v$.password.password.$error" class="error-msg">
                *Password deve ter pelo menos 8 caracteres
              </span>
            </q-card-section>
            <q-card-section class="q-pb-xs q-pt-xs">
              <q-input
                class="input_stuff"
                v-model="state.password.confirm"
                outlined
                dense
                type="password"
                label="Confirmar Password"
                color="secondary"
                label-color="secondary"
                input-style="color:white"
              />
              <span v-if="v$.password.confirm.$error" class="error-msg">
                *Passwords não correspondem
              </span>
            </q-card-section>
          </q-scroll-area>

          <q-card-section class="q-pb-xs q-pt-xs">
            <q-checkbox
              v-model="terms"
              color="secondary"
              label="Aceito os termos"
            />
          </q-card-section>

          <p v-if="!terms" class="more">
            * Precisa de aceitar os termos para criar uma conta
          </p>
          <p class="more">
            Já tem conta? Faça login
            <router-link to="/login" style="color: #ff8798">aqui</router-link>
          </p>
          <q-card-section>
            <q-btn
              color="secondary"
              text-color="black"
              class="login_btn"
              label="Criar conta"
              @click="submit"
            >
              <q-popup-proxy id="popup-proxy" style="display: none">
                <q-banner
                  :class="
                    feedback.type == 'success' ? 'bg-green-9' : 'bg-red-9'
                  "
                >
                  <template v-slot:avatar>
                    <q-icon
                      :name="feedback.type == 'success' ? 'done' : 'error'"
                      color="primary"
                    />
                  </template>
                  {{ feedback.text }}
                </q-banner>
              </q-popup-proxy>
            </q-btn>
          </q-card-section>
        </q-card>
      </div>
      <div class="column">
        <img src="../assets/register/1.png" class="background1" />
        <img src="../assets/register/slogan.png" class="background2" />
      </div>
    </div>
  </div>
</template>

<script>
import { reactive, computed, ref } from "vue";
import useVuelidate from "@vuelidate/core";
import { required, email, minLength, sameAs } from "@vuelidate/validators";
import axios from "axios";
import URL from "../url.js";
export default {
  setup() {
    const state = reactive({
      username: "",
      email: "",
      password: {
        password: "",
        confirm: "",
      },
    });

    const feedback = ref({
      text: "",
      type: "",
    });

    const terms = ref(false);

    const rules = computed(() => {
      return {
        username: { required },
        email: { required, email },
        password: {
          password: { required, minLength: minLength(8) },
          confirm: { required, sameAs: sameAs(state.password.password) },
        },
      };
    });

    const v$ = useVuelidate(rules, state);

    return {
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
      state,
      terms,
      v$,
      feedback,
    };
  },
  methods: {
    async submit() {
      this.v$.$validate(); // checks all inputs
      if (!this.v$.$error) {
        // if ANY fail validation
        const result = await axios({
          method: "post",
          url: URL.URL + "/utilizador",
          data: {
            email: this.state.email,
            password: this.state.password.password,
            nickname: this.state.username,
            data_nascimento: "2000-06-04T12:39:48.792613",
          },
        });

        const result_data = await result.data;
        if (result_data == -1) {
          this.feedback.text = "Email já existe";
          this.feedback.type = "error";
        }
        if (result_data == 0) {
          this.feedback.text = "Username já existe";
          this.feedback.type = "error";
        }
        if (result_data == 1) {
          this.feedback.text = "Conta criada com sucesso";
          this.feedback.type = "success";
          setTimeout(() => {
            this.$router.push("/login");
          }, 1000);
        }
      } else {
        this.feedback.text = "Ocorreu um erro! Verifique os campos.";
        this.feedback.type = "error";
      }
      setTimeout(() => {
        const popupproxy = document.getElementById("popup-proxy");
        popupproxy.style.display = "block";
      }, 100);
    },
  },
};
</script>

<style scoped>
.register {
  display: flex;
  flex-direction: column;
  max-width: 20%;
  margin-left: 15%;
  margin-top: 1%;
  z-index: 2;
}

.input_stuff {
  width: 100%;
  border: 2px solid #ffd208;
  border-radius: 10px;
}

.row {
  display: flex;
  flex-direction: row;
  justify-content: space-between;
}
.logo {
  z-index: 2;
  width: 80%;
  margin-left: 10%;
}
.my-card {
  z-index: 0;
  margin-top: -19%;
  padding-top: 12%;
  padding-left: 10%;
  padding-right: 10%;
  border-radius: 10px;
  border: 2px solid #ffd208;
  height: 80vh;
}

.text {
  font-size: 40px;
  font-weight: bold;
}

.background2 {
  max-width: 100%;
}

.background1 {
  max-width: 100%;
  margin-bottom: 100px;
  z-index: 0;
}

.error-msg {
  color: white;
  font-size: 12px;
  margin-top: 5px;
}

.more {
  color: #ffd208;
  font-size: 12px;
  margin-top: 5px;
}

.column {
  margin-top: 100px;
  display: flex;
  flex-direction: column;
  max-width: 50%;
  margin-right: 2%;
}

.epic_games_logo {
  position: absolute;
  z-index: 1;
  left: 1%;
  top: 1%;
  max-width: 50px;
}

.login_btn {
  font-weight: bold;
}

.login_btn:hover {
  transform: scale(1.05);
}

.abs {
  position: absolute;
  z-index: 1;
  right: 45%;
  bottom: 25%;
  max-width: 400px;
}

.abs2 {
  position: absolute;
  z-index: 1;
  top: 15%;
  left: 4%;
  max-width: 400px;
}

.q-checkbox {
  justify-content: start;
}

.box {
  height: 100vh;
}

.box_campos {
  height: 43%;
  margin-top: 20px;
}

@media only screen and (max-width: 600px) {
  .background1 {
    display: none;
  }
  .register {
    max-width: 80%;
    margin: auto;
  }
  .abs {
    display: none;
  }
  .abs2 {
    display: none;
  }
  .background2 {
    margin: auto;
  }

  .column {
    display: initial;
    margin: auto;
    margin-top: 5%;
  }

  .box {
    height: 100%;
  }
}

@media only screen and (max-width: 1200px) {
  .background1 {
    display: none;
  }
  .register {
    max-width: 80%;
    margin: auto;
    margin-top: 1%;
  }

  .background2 {
    margin: auto;
  }

  .column {
    display: initial;
    margin: auto;
    margin-top: 5%;
  }

  .my-card {
    margin-top: -18%;
    padding-top: 16%;
  }

  .abs {
    right: 0%;
    bottom: 0%;
    max-width: 400px;
  }

  .abs2 {
    position: absolute;
    z-index: 1;
    top: 15%;
    left: 4%;
    max-width: 400px;
  }
  .box {
    height: 100%;
  }
}
</style>
