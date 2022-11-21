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
            <div class="text">Login</div>
          </q-card-section>

          <q-separator dark inset />
          <q-card-section class="q-pb-xs">
            <q-input
              class="input_stuff"
              v-model="state.email"
              outlined
              dense
              label="E-mail"
              color="secondary"
              label-color="secondary"
              input-style="color:white"
            />
            <span v-if="v$.email.$error" class="error-msg">
              *Insira um enderço de e-mail válido
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
              *Campo obrigatório
            </span>
          </q-card-section>

          <p class="more">
            Ainda não tem conta?
            <router-link to="/" style="color: #ff8798">Criar conta</router-link>
          </p>
          <q-card-section>
            <q-btn
              color="secondary"
              text-color="black"
              class="login_btn"
              label="Login"
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
import { required, email } from "@vuelidate/validators";
import axios from "axios";
import URL from "../url.js";
export default {
  setup() {
    const state = reactive({
      email: "",
      password: {
        password: "",
      },
    });

    const rules = computed(() => {
      return {
        email: { required, email },
        password: {
          password: { required },
        },
      };
    });

    const v$ = useVuelidate(rules, state);

    const feedback = ref({
      text: "",
      type: "",
    });
    return {
      state,
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
          url: URL.URL + "/utilizador/login",
          data: {
            email: this.state.email,
            password: this.state.password.password,
          },
        });

        const result_data = await result.data;

        if (result_data) {
          this.feedback.text = "Login feito com sucesso!";
          this.feedback.type = "success";
          //send to local storage

          localStorage.id = result_data.id;
          setTimeout(() => {
            this.$router.push("/main");
          }, 1000);
        } else {
          this.feedback.text = "Email ou password incorretos!";
          this.feedback.type = "error";
        }
      } else {
        this.feedback.text = "Ocorreu um erro!";
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
}

.text {
  font-size: 40px;
  font-weight: bold;
  margin-left: 25%;
}

.background2 {
  max-width: 100%;
}

.login_btn {
  font-weight: bold;
}

.login_btn:hover {
  transform: scale(1.05);
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

.input_stuff {
  width: 100%;
  border: 2px solid #ffd208;
  border-radius: 10px;
}

.box {
  height: 100vh;
}

@media only screen and (max-width: 600px) {
  .background1 {
    display: none;
  }
  .register {
    max-width: 80%;
    margin: auto;
    margin-top: 5%;
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
    height: 100vh;
  }
}

@media only screen and (max-width: 1200px) {
  .background1 {
    display: none;
  }
  .register {
    max-width: 80%;
    margin: auto;
    margin-top: 5%;
  }

  .background2 {
    margin: auto;
  }

  .column {
    display: initial;
    margin: auto;
    margin-top: 5%;
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
    height: 100vh;
  }
}
</style>
