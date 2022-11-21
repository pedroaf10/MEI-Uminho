package com.gamehub.Services;

import com.gamehub.Model.Users.Gamer;
import com.gamehub.Model.Users.Utilizador;
import com.gamehub.Repositories.JogoRepository;
import com.gamehub.Repositories.UtilizadorRepository;
import org.springframework.beans.factory.annotation.Autowired;
import org.springframework.stereotype.Service;

import java.util.ArrayList;
import java.util.List;
import java.util.Optional;

@Service
public class UtilizadorService {

    @Autowired
    private UtilizadorRepository utilizadorRepository;

    @Autowired
    private JogoRepository jogoRepository;

    /**
     * Método para inserir um novo utilizador
     * @param utilizador utilizador a inserir
     * @return -1 se o email já existe, 0 se o username já existe ou 1 caso seja inserido com sucesso
     */
    public int insertUtilizador(Utilizador utilizador) {
        int emailAlreadyExists = utilizadorRepository.existeEmail(utilizador.getEmail()).intValue();
        if (emailAlreadyExists == 1) {
            return -1;
        } else {
            int usernameAlreadyExists = utilizadorRepository.existeUsername(utilizador.getGamer().getNome()).intValue();
            if (usernameAlreadyExists == 1) {
                return 0;
            } else {
                utilizadorRepository.save(utilizador);
                return 1;
            }
        }


    }

    /**
     * Método que realiza o login de um utilizador
     * @param email email inserido
     * @param password password inserida
     * @return o gamer correspondete à sessão iniciada
     */
    public Gamer realiza_login(String email, String password) {

        List<Utilizador> utilizadores = this.getUtilizadorByEmail(email);
        Utilizador utilizador = null;
        Gamer g = null;

        for (Utilizador u : utilizadores) {
            if (u.getPassword().equals(password)) {
                utilizador = u;
            }
        }

        if (utilizador != null) {
            g = utilizador.getGamer();
            g.setEstado("Online");

            this.utilizadorRepository.save(utilizador);
        }

        return g;
    }

    /**
     * Método que retorna todos os utilizadores
     * @return Lista de todos os utilizadores
     */
    public List<Utilizador> getAllUtilizadores() {
        List<Utilizador> utilizadores = new ArrayList<>();
        utilizadorRepository.findAll().forEach(utilizadores::add);
        return utilizadores;
    }

    /**
     * Obter um utilizador a partir do seu ID
     * @param id id do utilizador
     * @return utilizador encontrado
     */
    public Utilizador getUtilizadorById(int id) {
        Optional<Utilizador> res = utilizadorRepository.findById(id);
        return res.orElse(null);
    }

    /**
     * Procura um utilizador dado o seu email
     * @param email email do utilizador
     * @return utilizador encontrado
     */
    public List<Utilizador> getUtilizadorByEmail(String email) {
        return utilizadorRepository.findByEmail(email);
    }
}
